/*
 * IntervalElement.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.intervals;

import java.util.*;

import org.jakstab.analysis.*;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Characters;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;

/**
 * A reduced signed (twos complement) bitvector interval element with region and stride information. 
 * An IntervalElement represents the numbers
 * {region:(left + k*stride) | k \in [0 .. (right-left)/stride]}
 * For intervals of size 1, the stride is 0 by definition. The interval is reduced, i.e. its right 
 * limit is included (the size of the interval is a multiple of its stride). 
 * All values are represented as signed long integers, with left < right.
 * 
 * @author Johannes Kinder
 */
public class IntervalElement implements AbstractDomainElement, BitVectorType, Iterable<Long> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalElement.class);
	
	private static final int MAX_CONCRETIZATION_SIZE = 100;
	
	public static IntervalElement TRUE = new IntervalElement(ExpressionFactory.TRUE);
	public static IntervalElement FALSE = new IntervalElement(ExpressionFactory.FALSE);
	
	private final long left;
	private final long right;
	private final int bitWidth;
	private final long stride;
	private final MemoryRegion region;

/*integrity :: Ival -> Bool
integrity (Ival s l r) =
     (s == (-1) && l == 0 && r == 0)
  || (s == 0 && l == r)
  || (s > 0 && r >= l && ((r - l) `div` s) * s + l == r)*/
	private Boolean integrity() {
		return
			bitWidth > 1 && bitWidth <= 64
		&&	left >= minBW(getBitWidth()) && right <= maxBW(getBitWidth())
		&&(	stride == 0 && left == 1 && right == 0		//bot
		||	stride == 0 && left == right				//singleton
		||	stride > 0 && (right - left) % stride == 0	//normal + top
		);
	}
	
	public IntervalElement(RTLNumber number) {
		this(number, number);
	}
	
	public IntervalElement(RTLNumber startNumber, RTLNumber endNumber) {
		this(MemoryRegion.GLOBAL, startNumber, endNumber);
	}
	
	public IntervalElement(MemoryRegion region, RTLNumber startNumber, RTLNumber endNumber) {
		this(region, startNumber.longValue(), endNumber.longValue(), 1, startNumber.getBitWidth());
		assert startNumber.getBitWidth() == endNumber.getBitWidth();
	}
	
	public IntervalElement(MemoryRegion region, RTLNumber number) {
		this(region, number.longValue(), number.longValue(), 0, number.getBitWidth());
	}
	
	public IntervalElement(MemoryRegion region, long left, long right, long stride, int bitWidth) {
/*ival s l r
           | s < 0 = Ival (-1) 0 0
           | r < l  = ival s r l
           | l == r || s == 0 = Ival 0 l l
           | integrity tmp = tmp
           | otherwise = ival s l $ ((r - l) `div` s) * s + l
  where tmp = Ival s l r*/
		this.region = region;
		this.bitWidth = bitWidth;
		if(right < left) {
			logger.info("creating bot element");
			this.left = 1;
			this.right = 1;
			this.stride = 0;
		} else if(left == right) {
			this.left = left;
			this.right = right;
			this.stride = 0;
		} else {
			this.left = left;
			this.stride = stride;
			this.right = ((right - left) / stride) * stride + left; //adjust to reduced border
			if(this.right != right)
				logger.info("ajdusted right border to reduction: " + right + " -> " + this.right);
		}
		assert integrity() : "tried to create invalid interval";
	}
	
	public long getLeft() {
		return left;
	}

	public long getRight() {
		return right;
	}
	
	public long size() {
		if (isBot()) return 0;
		if (stride == 0) return 1;
		return (right - left)/stride + 1;
	}
	
	public MemoryRegion getRegion() {
		return region;
	}

	@Override
	public int getBitWidth() {
		return bitWidth;
	}
	
	public long getStride() {
		return stride;
	}

	public static IntervalElement getTop(int bitWidth) {
		return new IntervalElement(MemoryRegion.TOP, minBW(bitWidth), maxBW(bitWidth), 1, bitWidth);
	}

	public static IntervalElement getBot(int bitWidth) {
		//XXX scm: global region for top?
		return new IntervalElement(MemoryRegion.GLOBAL, 1, 0, 1, bitWidth);
	}
	
	/**
	 * Widening by extending the interval bounds infinitely into the direction of 
	 * the parameter. Takes care to preserve singleton-property of top elements.
	 * 
	 * @param towards the target towards which this element should be widened.
	 * @return the result of the widening, which is greater than this and the
	 *         parameter interval.
	 */
	public IntervalElement widen(IntervalElement towards) {
		assert towards.bitWidth == bitWidth;
		IntervalElement result;
		IntervalElement top = getTop(bitWidth);
		if(isBot()) return towards;
		if(towards.isBot()) return this;
		if (region != towards.region) return top;
		long newStride = joinStride(towards);
		
		if (towards.left < left) {
			if (towards.right > right || rightOpen()) {
				result = top;
			} else {
				result = new IntervalElement(region, top.getLeft() + (right - top.getLeft()) % newStride, right, newStride, bitWidth);
			}
		} else {
			if (towards.right > right) {
				if (leftOpen()) {
					result = top; 
				} else {
					result = new IntervalElement(region, left, top.getRight() - (top.getRight() - left) % newStride, newStride, bitWidth);
				}
			} else {
				if (newStride > stride)
					result = new IntervalElement(region, left, right, newStride, bitWidth);
				else
					result = this;
			}
		}
		// if (this != result) logger.debug("Widening " + this + " to " + result);
		assert lessOrEqual(result) : "Widening unsound!";
		return result;
	}

	/*
	 * @see org.jakstab.analysis.AbstractValue#concretize()
	 */
	@Override
	public Set<RTLNumber> concretize() {
		// magic max size for jump tables
		if (getRegion() != MemoryRegion.GLOBAL || size() > MAX_CONCRETIZATION_SIZE) {
			return RTLNumber.ALL_NUMBERS;
		}
		Set<RTLNumber> result = new FastSet<RTLNumber>();
		
		if(!isBot()) {
			if (stride == 0)
				result.add(ExpressionFactory.createNumber(left, bitWidth));
			else
				for (long v : this)
					result.add(ExpressionFactory.createNumber(v, bitWidth));
		}
		return result;
	}

	/*
	 * @see org.jakstab.analysis.AbstractValue#join(org.jakstab.analysis.LatticeElement)
join :: Ival -> Ival -> Ival
join a@(Ival s1 l1 r1) b@(Ival s2 l2 r2)
  | isBot a = b
  | isBot b = a
  | isTop a || isTop b = top
  | otherwise = ival s l r
  where
  s = gcd (gcd s1 s2) (abs $ l1 - l2)
  l = min l1 l2
  r = max r1 r2
	 */
	@Override
	public IntervalElement join(LatticeElement lt) {
		IntervalElement other = (IntervalElement)lt;
		assert bitWidth == other.bitWidth;
		if (isTop() || other.isBot()) return this;
		if (isBot() || other.isTop()) return other;
		if (this.region != other.region) return getTop(bitWidth);
		
		long newStride = joinStride(other);
		long l = Math.min(this.left, other.left);
		long r = Math.max(this.right, other.right);
		
		return new IntervalElement(this.region, l, r, newStride, bitWidth);
	}
	
	private long joinStride(IntervalElement other) {
		long newStride;
		// If both intervals were size 1, set stride to difference
		if (this.stride == 0 && other.stride == 0)
			newStride = Math.abs(other.left - this.left);
		else {
			newStride = gcd(stride, other.stride);
			newStride = gcd(newStride, Math.abs(left - other.left));
		}
		return newStride;
	}
	

	/*
	 * @see org.jakstab.analysis.LatticeElement#isBot()
	 */
	@Override
	public boolean isBot() {
		//XXX scm: What about region?
		return getStride() == 0 && getLeft() == 1 && getRight() == 0;
	}

	/*
	 * @see org.jakstab.analysis.LatticeElement#isTop()
	 */
	@Override
	public boolean isTop() {
		//XXX scm: What about region?
		return getStride() == 1 && getLeft() == minBW(getBitWidth()) && getRight() == maxBW(getBitWidth());
	}
	
	/*
	 * @see org.jakstab.analysis.LatticeElement#lessOrEqual(org.jakstab.analysis.LatticeElement)
	 */
	@Override
	public boolean lessOrEqual(LatticeElement l) {
		IntervalElement other = (IntervalElement)l;
		assert getBitWidth() == other.getBitWidth();
		assert getRegion() == other.getRegion();
		return
			isBot()
		||	other.isTop()
		||	!other.isBot() && getLeft() >= other.getLeft() && getRight() <= other.getRight() && (other.getStride() == 0 || getStride() % other.getStride() == 0);
	}

	/*
	 * @see java.lang.Object#toString()
	 */
	@Override
	public String toString() {
		if (isTop()) return Characters.TOP;
		if (isBot()) return Characters.BOT;
		StringBuilder s = new StringBuilder();
		if (region != MemoryRegion.GLOBAL) 
			s.append(region).append(":");

		s.append(stride);
		s.append('[');

		if (leftOpen()) { 
			s.append(Characters.TOP); 
		} else {
			s.append(left);
		}
		if (size() == 1) {
			s.append(']');
		} else {
			s.append(';');
			if (rightOpen()) { 
				s.append(Characters.TOP); 
			} else {
				s.append(right);
			}
			s.append(']');
		}
		return s.toString(); 
	}

	/*
	 * @see java.lang.Object#hashCode()
	 */
	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + bitWidth;
		result = prime * result + (int)stride;
		result = prime * result + (int) (left ^ (left >>> 32));
		result = prime * result + ((region == null) ? 0 : region.hashCode());
		result = prime * result + (int) (right ^ (right >>> 32));
		return result;
	}

	/*
	 * @see java.lang.Object#equals(java.lang.Object)
	 */
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		IntervalElement other = (IntervalElement) obj;
		if (bitWidth != other.bitWidth)
			return false;
		if (stride != other.stride)
			return false;
		if (left != other.left)
			return false;
		if (region == null) {
			if (other.region != null)
				return false;
		} else if (!region.equals(other.region))
			return false;
		if (right != other.right)
			return false;
		return true;
	}

	public boolean leftOpen() {
		return getLeft() == getTop(bitWidth).getLeft();
	}
	
	public boolean rightOpen() {
		return getRight() == getTop(bitWidth).getRight();
	}
	
	/**
	 * Addition of two strided interval elements. Code adapted from Gogul Balakrishnan's thesis.
	 * 
	 * @param op the interval to add to this interval
	 * @return A new interval that is the sum of this and the given interval
	 */
	@Override
	public IntervalElement plus(AbstractDomainElement other) {
		
		IntervalElement op = (IntervalElement)other;
		assert bitWidth == op.bitWidth;
		if(isBot() || op.isBot()) return getBot(bitWidth);
		MemoryRegion newRegion = region.join(op.region);
		if (newRegion.isTop()) return getTop(bitWidth);

		long l = this.left + op.left;
		long r = this.right + op.right;
		long u = this.left & op.left & ~l & ~(this.right & op.right & ~r);
		long v = ((this.left ^ op.left) | ~(this.left ^ l)) & (~this.right & ~op.right & r);
		if ((u | v) < 0 || 
				(u | v) > getTop(bitWidth).right) {
			return getTop(bitWidth);
		}
		
		return new IntervalElement(newRegion, l, r, gcd(stride, op.stride), bitWidth);
	}
	
	@Override
	public IntervalElement negate() {
		if(isBot()) return this;
		if (left == getTop(bitWidth).left) {
			// If this interval is just the minimum value, it's negation is the same value again in 2s complement.
			if (left == right) return this;
			return getTop(bitWidth);
		} else {
			return new IntervalElement(region, -right, -left, stride, bitWidth);
		}
	}

	private static long gcd(long a, long b) {
		assert a >= 0 && b >= 0 : "call to gcd with negative argument";
		while(b != 0) {
			long tmp = a;
			a = b;
			b = tmp % b;
		}
		return a;
	}


	/**
	 * Multiplies two interval elements.
	 * 2[0;4] * 1[3;6]  = 2[0;24]
	 * 0,2,4  * 3,4,5,6 = 0,6,8,10,12,16,20,24
	 * 
	 * 3[0;9]  * 0[6;6] = 18[0;54]
	 * 0,3,6,9 * 5      = 0,18,36,54
	 * 
	 * 3[-3;6]  * 2[4;8]  = 6[-24;48]
	 * -3,0,3,6 * 4,6,8   = -24,-18,-12,0,12,18,24,36,48

	 * @param op the other interval element to multiply this element with.
	 * @return a new interval element which is the result of the multiplication.
	 */
	@Override
	public IntervalElement multiply(AbstractDomainElement other) {

		IntervalElement op = (IntervalElement)other;

		if(isBot() || op.isBot()) return getBot(bitWidth);

		MemoryRegion newRegion = region.join(op.region);
		int newBitWidth = bitWidth * 2; 
		IntervalElement top = getTop(newBitWidth);
		// Cannot multiply a pointer
		if (newRegion != MemoryRegion.GLOBAL) return top;
		
		// Try all combinations of mutltiplying the bounds
		// yeah, it's a hack, but it works.
		long[] b = new long[4];
		b[0] = getLeft() * op.getLeft();
		b[1] = getLeft() * op.getRight();
		b[2] = getRight() * op.getLeft();
		b[3] = getRight() * op.getRight();
		Arrays.sort(b);

		if (b[0] <= top.getLeft() || b[3] >= top.getRight())
			return top;

		long newStride;
		if (stride == 0) {
			if (op.stride == 0) newStride = 0;
			else {
				assert left == right;
				newStride = op.stride * Math.abs(left);
			}
		} else if (op.stride == 0) {
			assert op.left == op.right;
			newStride = Math.abs(op.left) * stride; 
		} else {
			newStride = stride * op.stride;
		}
		
		return new IntervalElement(region, b[0], b[3], newStride, 
				newBitWidth);
	}
	
	public IntervalElement bitExtract(int first, int last) {
		if(isBot()) return this;
		int newBitWidth = last - first + 1;
		if (region == MemoryRegion.GLOBAL) {
			// Check if operand is already within bit range. No bit range 
			// extraction is actually performed.
			IntervalElement top = IntervalElement.getTop(newBitWidth);
			if (first == 0 && left >= top.getLeft() && right <= top.getRight()) {
				IntervalElement newElement = 
					new IntervalElement(MemoryRegion.GLOBAL, left, 
							right, stride, newBitWidth);
				return newElement;
			}
		}
		return IntervalElement.getTop(newBitWidth);	
	}
	
	public IntervalElement signExtend(int first, int last) {
		if(isBot()) return this;
		int newBitWidth = Math.max(bitWidth, last + 1);
		if (region == MemoryRegion.GLOBAL) {
			// If region is global, return the value with new bit width
			return new IntervalElement(region,
					left, right, stride,
					newBitWidth);
		} 
		return IntervalElement.getTop(newBitWidth);
	}

	public IntervalElement zeroFill(int first, int last) {
		if(isBot()) return this;
		int newBitWidth = Math.max(bitWidth, last + 1);
		if (region == MemoryRegion.GLOBAL && left >= 0 && right < (1 << first)) {
			// If value is non-negative and does not set any
			// bits that are zeroed out, it is unmodified
			return new IntervalElement(region,
					left, right, stride,
					newBitWidth);
		} 
		return IntervalElement.getTop(newBitWidth);
	}

	@Override
	public Iterator<Long> iterator() {
		return new Iterator<Long>() {
			long cursor = left;
			long incr = stride == 0 ? 1 : stride;

			public void remove() {
				throw new UnsupportedOperationException();
			}
			
			public Long next() {
				if (!hasNext()) throw new NoSuchElementException();
				long r = cursor;
				cursor += incr;
				return r;
			}
			
			public boolean hasNext() {
				return cursor <= right;
			}
		};
	}

	@Override
	public boolean hasUniqueConcretization() {
		return size() == 1;
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {

		if(isBot()) return this;
		if (isTop()) return IntervalElement.getTop(bitWidth);
		
		AbstractDomainElement res = null;
		for(long offset : this) {
			AbstractDomainElement read = store.get(getRegion(), offset, bitWidth);
			if(res == null)
				res = read;
			else
				res = res.join(read);
		}
		return res;
	}

	@Override
	public Collection<? extends AbstractDomainElement> readStorePowerSet(
			int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		
		if(isBot()) return Collections.singleton(getBot(bitWidth));
		if (isTop() || size() > MAX_CONCRETIZATION_SIZE) 
			return Collections.singleton(getTop(bitWidth));
		
		Set<AbstractDomainElement> res = new FastSet<AbstractDomainElement>();
		for (long offset : this) {
			res.add(store.get(getRegion(), offset, bitWidth));
		}
		return res;
	}

	@Override
	public <A extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<A> store, A value) {
		if(isBot()) return;
		if (!getRegion().isSummary() && size() == 1) {
			// Strong update
			store.set(getRegion(), 
					getLeft(), 
					bitWidth, value);
		} else {
			// Weak update
			if (getRegion().isTop() || size() > 100)
				store.setTop(getRegion());
			else {
				for (long i : this) {
					store.weakUpdate(getRegion(), i, bitWidth, value);
				}
			}
			
		}
	}

	private static long maxBW(int bitWidth) {
		if(bitWidth == 1) return 1;
		return (1l << (bitWidth - 1)) - 1;
	}
	private static long minBW(int bitWidth) {
		if(bitWidth == 1) return 0;
		return -maxBW(bitWidth) - 1;
	}


}
