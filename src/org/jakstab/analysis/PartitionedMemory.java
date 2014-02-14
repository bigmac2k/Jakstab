/*
 * PartitionedMemory.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */
package org.jakstab.analysis;

import java.io.IOException;
import java.util.*;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.asm.AbsoluteAddress;
import org.jakstab.loader.ExecutableImage;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

/**
 * @author Johannes Kinder
 */
public final class PartitionedMemory<A extends AbstractValue> implements LatticeElement {

	protected final class MemoryCell {
		final long offset;
		final int size;
		final A contents;

		private MemoryCell(long offset, int size, A contents) {
			super();
			this.contents = contents;
			this.offset = offset;
			this.size = size;
		}

		public String toString() {
			return contents.toString();
		}

		@Override
		public int hashCode() {
			final int prime = 31;
			int result = 1;
			result = prime * result
					+ ((contents == null) ? 0 : contents.hashCode());
			result = prime * result + (int) (offset ^ (offset >>> 32));
			result = prime * result + size;
			return result;
		}

		@Override
		public boolean equals(Object obj) {
			if (this == obj)
				return true;
			if (obj == null)
				return false;
			if (!(obj instanceof PartitionedMemory.MemoryCell))
				return false;
			@SuppressWarnings("unchecked")
			MemoryCell other = (MemoryCell) obj;
			if (contents == null) {
				if (other.contents != null)
					return false;
			} else if (!contents.equals(other.contents))
				return false;
			if (offset != other.offset)
				return false;
			if (size != other.size)
				return false;
			return true;
		}
	}

	private static final Logger logger = Logger.getLogger(PartitionedMemory.class);
	
	private final LazyHashMapMap<MemoryRegion, Long, MemoryCell> store;
	private boolean dataIsTop;
	private final AbstractValueFactory<A> valueFactory;
	
	public PartitionedMemory(AbstractValueFactory<A> valueFactory) {
		this.valueFactory = valueFactory;
		store = new LazyHashMapMap<MemoryRegion, Long, MemoryCell>();
		dataIsTop = false;
	}
	
	public PartitionedMemory(PartitionedMemory<A> proto) {
		valueFactory = proto.valueFactory;
		dataIsTop = proto.dataIsTop;
		store = new LazyHashMapMap<MemoryRegion, Long, MemoryCell>(proto.store);
	}
	
	public void setTop() {
		if (Options.ignoreWeakUpdates.getValue()) {
			logger.warn("Ignoring weak universal update!");
			return;
		}
		store.clear();
		dataIsTop = true;
		logger.info("Overapproximated all memory regions to TOP!");
		if (Options.debug.getValue())
			throw new UnknownPointerAccessException("Set all memory regions to TOP!");
	}
	
	public void setTop(MemoryRegion region) {
		if (region == MemoryRegion.TOP) {
			setTop();
			return;
		}

		if (Options.ignoreWeakUpdates.getValue()) {
			logger.warn("Ignoring weak update to " + region);
			return;
		}

		if (store.containsLeftKey(region))
			store.remove(region);
		if (region == MemoryRegion.GLOBAL)
			dataIsTop = true;

		logger.info("Overapproximated all of " + region + " to TOP!");
		if (Options.debug.getValue() && (region == MemoryRegion.STACK || region == MemoryRegion.GLOBAL))
			throw new UnknownPointerAccessException("Set all of "+region+" to TOP!");
	}
	
	private void setBytesTop(MemoryRegion region, long offset, int size) {
		for (int i=0; i<size; i++) {
			// We need to explicitly remember TOP memory cells in the global region,
			// as it is initialized to the static data of the executable.
			// If heap cells are assumed to be initially BOT, we also need to do this.
			if ((Options.initHeapToBot.getValue() && region != MemoryRegion.STACK) || region == MemoryRegion.GLOBAL) {
				MemoryCell topCell = new MemoryCell(offset + i, 1, 
						valueFactory.createTop(8));
				store.put(region, offset + i, topCell);
			} else {
				store.remove(region, offset + i);
			}
		}
	}
	
	/**
	 * Sets a value at an offset in a memory region. If any existing memory
	 * cells are partially overwritten, sets the memory cell at the original
	 * offset to TOP. Other copies of the cell at intermediate offsets do 
	 * not need to be overwritten.
	 * 
	 * A A A A B B[B]B C C C C    <- Write 1-byte X to offset 6
	 * A A A A T B X B C C C C
	 *
	 * A A A A B B B[B C]C C C    <- Write 2 byte X to offset 7
	 * A A A A T B B X X C C C    <- B is set to top at its original offset
	 * 							     C is not changed, as its overwritten anyway
	 * 
	 * 
	 * @param region The memory region to access, cannot be TOP
	 * @param offset The offset to write to
	 * @param bitWidth Number of bits of the memory access
	 * @param value The abstract value to write
	 */
	public void set(MemoryRegion region, long offset, int bitWidth, A value) {
		assert region != MemoryRegion.TOP;
		assert (!(value instanceof BitVectorType) || ((BitVectorType)value).getBitWidth() == bitWidth) : 
			"Memory access bitwidth " + bitWidth + " does not match bitwidth of value to set: " + ((BitVectorType)value).getBitWidth();

		int size = bitWidth / 8;
		
		// Set all old memory cells in the written area to top
		for (int i=0; i<size; i++) {
			MemoryCell oldCell = store.get(region, offset + i);

			if (oldCell != null) {
				setBytesTop(region, oldCell.offset, oldCell.size);
			}
		}
		
		// If we only wanted to set TOP and we're not in the global region, 
		// we are already done.
		if (!value.isTop() || region == MemoryRegion.GLOBAL) {

			// Separate update from deletion, so while overwriting an old cell, 
			// we don't have to be careful not to overwrite our new cell
			MemoryCell cell = new MemoryCell(offset, size, value);
			for (int i=0; i<size; i++) {
				store.put(region, offset + i, cell);
				logger.debug("i : " + i + " put " + cell + " at region " + region + " and offset " + Long.toHexString(offset + i) + "; result: " + store.get(region, offset + i) + " smart result: " + get(region, offset + i, bitWidth));
			}
		}
	}
	
	@SuppressWarnings("unchecked")
	public void weakUpdate(MemoryRegion region, long offset, int bitWidth, A value) {
		assert region != MemoryRegion.TOP;
		A oldValue = get(region, offset, bitWidth);
		
		// If we treat heap cells as initialized to BOT, just set uninitialized cells to the new value
		if (Options.initHeapToBot.getValue() && oldValue.isTop() && !store.containsKey(region, offset))
			set(region, offset, bitWidth, value);
		else
			set(region, offset, bitWidth, (A)value.join(oldValue));
	}
	
	public A get(MemoryRegion region, long offset, int bitWidth) {
		assert region != MemoryRegion.TOP;
		int size = bitWidth / 8;
		MemoryCell cell = store.get(region, offset);
		if (cell != null) {
			if (cell.offset != offset || cell.size != size) {
				
				// ,cell.offset
				// |   ,offset
				// |   |   ,cell.offset + cell.size
				// A A[A A]B B B B
				if (cell.size > size && (cell.offset + cell.size >= offset + size)) {
					// Extract bitrange from bigger cell
					int firstBit = (int)((offset - cell.offset) * 8);
					int lastBit = firstBit + bitWidth - 1;
					assert firstBit >= 0;
					
					A parentVal = cell.contents;

					Collection<RTLNumber> cValues = new LinkedList<RTLNumber>();
					for (RTLNumber cVal : parentVal.concretize()) {
						if (cVal == null) {
							cValues = null;
							break;
						}
						
						cValues.add(RTLBitRange.calculate(firstBit, lastBit, cVal));
					}
					if (cValues != null) {
						A e = valueFactory.createAbstractValue(cValues);
						//logger.debug("Generated abstract value " + e + " for mem" + bitWidth + "[" + region + " + " + offset + 
						//		"] from value " + parentVal + " of mem" + (cell.size * 8) + "[" + region + " + " + cell.offset + "]");
						return e;
					}
				} else if (cell.offset == offset && cell.size < size) {
					// Combine smaller cells to bigger one
					
					Collection<RTLNumber> lastValues = new LinkedList<RTLNumber>();
					lastValues.add(ExpressionFactory.createNumber(0, 8));
					
					Collection<RTLNumber> cValues = null;

					byteIteration: for (int i=0; i<size; i++) {
						cValues = new LinkedList<RTLNumber>();
						A byteVal = get(region, cell.offset + i, 8);
						for (RTLNumber cVal : byteVal.concretize()) {
							if (cVal == null) {
								cValues = null;
								break byteIteration;
							}
							
							for (RTLNumber last : lastValues) {
								long val = last.longValue();
								if (i < size - 1) {
									val = val | (0xFF & cVal.longValue()) << (i*8);
								} else {
									// do not mask the MSB with 0xFF, so we get sign extension for free
									val = val | (cVal.longValue() << i * 8);
								}
								cValues.add(ExpressionFactory.createNumber(val, (i+1)*8));
							}
						}
						lastValues = cValues;
					}

					if (cValues != null) {
						A e = valueFactory.createAbstractValue(cValues);
						return e;
					}
				}
					
					
				logger.debug("Mismatching get with bitwidth " + bitWidth + " on cell at " + region + " + " + offset + " with bitwidth " + cell.size * 8);
				
				return valueFactory.createTop(bitWidth);
			}
			return cell.contents;

		} else if (region == MemoryRegion.GLOBAL) {

			// Check if the memory location references the program's data area or imports
			AbsoluteAddress a = new AbsoluteAddress(offset);
			ExecutableImage module = Program.getProgram().getModule(a);
			logger.debug("getting memory for: " + a + " from: " + module + " dataIsTop: " + dataIsTop);
			// only read memory from image if we havn't overapproximated yet or it's a read only section
			if (module != null && (!dataIsTop || module.isReadOnly(a))) {
				RTLNumber mValue;
				try {
					mValue = module.readMemoryLocation(
							ExpressionFactory.createMemoryLocation(
									ExpressionFactory.createNumber(offset), bitWidth));
					// Memory outside the program area is implicitly initialized to top 
					if (mValue != null) 
						return valueFactory.createAbstractValue(mValue);
				} catch (IOException e) {
					// Fall through and return TOP
				}
			} 
		}		
		return valueFactory.createTop(bitWidth);
	}
	
	public void memcpy(MemoryRegion srcRegion, long srcOffset, 
			MemoryRegion dstRegion, long dstOffset, long size) {
		
		for (long i=0; i<size;) {
			long dstPtr = dstOffset + i;
			MemoryCell v = store.get(srcRegion, dstPtr);
			if (v != null && v.offset == dstPtr) {
				set(dstRegion, dstPtr, v.size * 8, v.contents);
				i += v.size;
			} else {
				set(dstRegion, dstPtr, 8, get(srcRegion, srcOffset + i, 8));
				i++;
			}
		}
	}
			

	
	/**
	 * Removes all elements from the stack below the passed stack offset.
	 * 
	 * @param offset the stack offset below which all entries should be cleared 
	 */
	public void forgetStackBelow(long offset) {
		Map<Long, MemoryCell> stack = store.getSubMap(MemoryRegion.STACK);
		if (stack == null)
			return;
		
		//stack.headMap(offset).clear();
//		for (Iterator<Long> it = stack.keySet().iterator(); it.hasNext();)
		for (Iterator<Map.Entry<Long, MemoryCell>> it = store.subMapIterator(MemoryRegion.STACK); it.hasNext();)
			if (it.next().getKey() < offset) {
				it.remove();
			}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public PartitionedMemory<A> join(LatticeElement l) {
		logger.debug("\n\n((((((((((Join\n");
		PartitionedMemory<A> other = (PartitionedMemory<A>)l;
		PartitionedMemory<A> result = new PartitionedMemory<A>(valueFactory);
		
		//global data region was set to top if one of the operands had it set to top already
		result.dataIsTop = dataIsTop || other.dataIsTop;

		// Join memory valuations. For the global region, we need to do both directions, 
		// because constant image data is not present in store, but only visible
		// through calls to get().
		if (store.containsLeftKey(MemoryRegion.GLOBAL)) {
			for (Map.Entry<Long, MemoryCell> entry : store.getSubMap(MemoryRegion.GLOBAL).entrySet()) {
				long offset = entry.getKey();
				if (offset != entry.getValue().offset) continue;
				int bitWidth = entry.getValue().size * 8;
				A value = entry.getValue().contents;
				A valueToSet = (A)value.join(other.get(MemoryRegion.GLOBAL, offset, bitWidth));
				result.set(MemoryRegion.GLOBAL, offset, bitWidth, 
						valueToSet);
				logger.debug("join reversed: set GLOBAL[" + Long.toHexString(offset) + "](" + bitWidth + ") = " + valueToSet + "; result: " + result.get(MemoryRegion.GLOBAL, offset, bitWidth));
			}
		}

		for (EntryIterator<MemoryRegion, Long, MemoryCell> entryIt = other.store.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
			long offset = entryIt.getRightKey();
			if (offset != entryIt.getValue().offset) continue;
			MemoryRegion region = entryIt.getLeftKey();
			int bitWidth = entryIt.getValue().size * 8;
			A value = entryIt.getValue().contents;
			A othergot = this.get(region, offset, bitWidth);
			A valueToSet = (A)value.join(othergot);
			result.set(region, offset, bitWidth, 
					valueToSet);
			logger.debug("join normal: set GLOBAL[" + Long.toHexString(offset) + "](" + bitWidth + ") = " + valueToSet + "; result: " + result.get(MemoryRegion.GLOBAL, offset, bitWidth));
		}

		logger.debug("op1: " + this + "\n\nop2: " + l + "\n\nres: " + result + "\n\nthis <= result: " + this.lessOrEqual(result) + "\nthat <= result: " + l.lessOrEqual(result));
		
		FastSet<Pair<MemoryRegion, Long>> keys = new FastSet<Pair<MemoryRegion, Long>>();
		for(EntryIterator<MemoryRegion, Long, MemoryCell> entryIt = store.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
			long offset = entryIt.getRightKey();
			logger.debug("offset: " + Long.toHexString(offset) + " cellOffset: " + Long.toHexString(entryIt.getValue().offset));
			if (offset != entryIt.getValue().offset) continue;
			MemoryRegion region = entryIt.getLeftKey();
			keys.add(new Pair<MemoryRegion, Long>(region, offset));
		}
		logger.debug("keys: " + keys);
		
		if(!(this.lessOrEqual(result) && l.lessOrEqual(result))) {
		for(Pair<MemoryRegion, Long> pair : keys) {
			MemoryCell thisMemCell = store.get(pair.getLeft(), pair.getRight());
			MemoryCell thatMemCell = other.store.get(pair.getLeft(), pair.getRight());
			MemoryCell resuMemCell = result.store.get(pair.getLeft(), pair.getRight());
			logger.debug();
			if(thisMemCell == null)
				logger.debug(pair.getLeft() + " this: " + Long.toHexString(pair.getRight()) + " = NULL, dataIsTop: " + dataIsTop);
			else
				logger.debug(pair.getLeft() + " this: (" + Long.toHexString(pair.getRight()) + "=" + Long.toHexString(thisMemCell.offset) + "[" + thisMemCell.size + "]  = " + thisMemCell.contents + " <= " + get(pair.getLeft(), pair.getRight(), thisMemCell.size * 8));
			if(thatMemCell == null)
				logger.debug(pair.getLeft() + " that: " + Long.toHexString(pair.getRight()) + " = NULL, dataIsTop: " + other.dataIsTop);
			else
				logger.debug(pair.getLeft() + " that: (" + Long.toHexString(pair.getRight()) + "=" + Long.toHexString(thatMemCell.offset) + "[" + thatMemCell.size + "]  = " + thatMemCell.contents + " <= " + other.get(pair.getLeft(), pair.getRight(), thatMemCell.size * 8));
			if(resuMemCell == null)
				logger.debug(pair.getLeft() + " resu: " + Long.toHexString(pair.getRight()) + " = NULL, dataIsTop: " + result.dataIsTop);
			else
				logger.debug(pair.getLeft() + " resu: (" + Long.toHexString(pair.getRight()) + "=" + Long.toHexString(resuMemCell.offset) + "[" + resuMemCell.size + "]  = " + resuMemCell.contents + " <= " + result.get(pair.getLeft(), pair.getRight(), resuMemCell.size * 8));
		}
		logger.debug("((\nthis <= result");
		this.lessOrEqual(result);
		logger.debug("that <= result");
		other.lessOrEqual(result);
		logger.debug("))");
		}
		logger.debug("))))))))))\n");
		//assert(this.lessOrEqual(result) && l.lessOrEqual(result));
		return result;
	}
	
	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return dataIsTop && store.isEmpty();
	}

	@SuppressWarnings("unchecked")
	@Override
	public boolean lessOrEqual(LatticeElement l) {
		// Check for every element in "other" if its value in "this" is less or equal 
		// than the value in "other". The elements not stored in the valuation maps 
		// of "other" (except for static data) are implicitly TOP and thus every value is less or equal to them.
		PartitionedMemory<A> other = (PartitionedMemory<A>)l;

		for (EntryIterator<MemoryRegion, Long, MemoryCell> entryIt = other.store.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
			long offset = entryIt.getRightKey();
			if (offset != entryIt.getValue().offset) continue;
			MemoryRegion region = entryIt.getLeftKey();
			int bitWidth = entryIt.getValue().size * 8;
			AbstractValue value = entryIt.getValue().contents;
			AbstractValue otherValue = get(region, offset, bitWidth);
			if (!otherValue.lessOrEqual(value))
				logger.debug("normal direction fail: " + Long.toHexString(offset) + ": " + otherValue + " <= " + value + " otherValue is top? " + otherValue.isTop() + " value is Top? " + value.isTop());
		}
		
		if (store.containsLeftKey(MemoryRegion.GLOBAL)) {
			for (Map.Entry<Long, MemoryCell> entry : store.getSubMap(MemoryRegion.GLOBAL).entrySet()) {
				long offset = entry.getKey();
				if (offset != entry.getValue().offset) continue;
				int bitWidth = entry.getValue().size * 8;
				A value = entry.getValue().contents;
				A otherValue = other.get(MemoryRegion.GLOBAL, offset, bitWidth);
				if (!value.lessOrEqual(otherValue))
					logger.debug("reversed direction fail: " + Long.toHexString(offset) + ": " + value + " <= " + otherValue + " otherValue is top? " + otherValue.isTop() + " value is Top? " + value.isTop());
			}
		}
		for (EntryIterator<MemoryRegion, Long, MemoryCell> entryIt = other.store.entryIterator(); entryIt.hasEntry(); entryIt.next()) {
			long offset = entryIt.getRightKey();
			if (offset != entryIt.getValue().offset) continue;
			MemoryRegion region = entryIt.getLeftKey();
			int bitWidth = entryIt.getValue().size * 8;
			AbstractValue value = entryIt.getValue().contents;
			if (!get(region, offset, bitWidth).lessOrEqual(value))
				return false;
		}
		
		// Once static data is modified, the new value is present in the store maps. Thus
		// we can assume that all static values not present in both states are equal.
		// At this point, the only way "this" could not be less or equal than "other" is if 
		// "this"'s store map contains a value in the static data address range that is not
		// yet present in "other"'s store map (and thus would have been missed by the 
		// iteration above.
		
		// Now, check for every element in "this"'s global region (includes the static data 
		// range) whether its value is less or equal than the value of that element in 
		// "other". If one isn't less or equal, this means that element is still not in 
		// other's store map and has a non-initial value in this's store map (TOP or just 
		// another value).
		

		
		if (store.containsLeftKey(MemoryRegion.GLOBAL)) {
			for (Map.Entry<Long, MemoryCell> entry : store.getSubMap(MemoryRegion.GLOBAL).entrySet()) {
				long offset = entry.getKey();
				if (offset != entry.getValue().offset) continue;
				int bitWidth = entry.getValue().size * 8;
				A value = entry.getValue().contents;
				if (!value.lessOrEqual(other.get(MemoryRegion.GLOBAL, offset, bitWidth)))
					return false;
			}
		}

		return true;
	}

	@Override
	public String toString() {
		StringBuilder res = new StringBuilder();
		for (MemoryRegion region : store.leftKeySet()) {
			res.append(" ").append(region).append(": [");
			for (Map.Entry<Long, MemoryCell> entry : store.getSubMap(region).entrySet()) {
				if (entry.getValue().offset == entry.getKey()) {
					if (region.equals(MemoryRegion.GLOBAL))
						res.append("0x").append(Integer.toHexString(
								entry.getKey().intValue()));
					else
						res.append(entry.getKey());
					res.append("=").append(entry.getValue()).append(",");
				}
			}
			res.append("]");
		}
		res.append(" SData = " + (dataIsTop ? Characters.TOP : "intact"));

		return res.toString();
	}

	@Override
	public int hashCode() {
		return store.hashCode() + (dataIsTop ? 1 : 0);
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) return true;
		PartitionedMemory<?> other = (PartitionedMemory<?>) obj;		
		return dataIsTop == other.dataIsTop && store.equals(other.store); 
	}
	
	public EntryIterator<MemoryRegion, Long, A> entryIterator() {
		return new MemoryIterator();
	}
	
	private class MemoryIterator implements EntryIterator<MemoryRegion, Long, A> {

		private EntryIterator<MemoryRegion, Long, MemoryCell> storeIt = 
			store.entryIterator();
		
		@Override
		public MemoryRegion getLeftKey() {
			return storeIt.getLeftKey();
		}

		@Override
		public Long getRightKey() {
			return storeIt.getRightKey();
		}

		@Override
		public A getValue() {
			return storeIt.getValue().contents;
		}

		@Override
		public boolean hasEntry() {
			return storeIt.hasEntry();
		}

		@Override
		public void next() {
			storeIt.next();
			while (storeIt.hasEntry() && storeIt.getRightKey() != storeIt.getValue().offset)
				storeIt.next();
		}
	}
}
