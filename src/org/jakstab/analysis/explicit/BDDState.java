package org.jakstab.analysis.explicit;

import java.util.*;

import org.jakstab.Options;
import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.ExpressionVisitor;
import org.jakstab.rtl.expressions.LongBWToRTLNumberCaster;
import org.jakstab.rtl.expressions.Operator;
import org.jakstab.rtl.expressions.RTLBitRange;
import org.jakstab.rtl.expressions.RTLConditionalExpression;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNondet;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLNumberIsDynBounded;
import org.jakstab.rtl.expressions.RTLNumberIsDynBoundedBits;
import org.jakstab.rtl.expressions.RTLNumberIsOrdered;
import org.jakstab.rtl.expressions.RTLNumberToLongBWCaster;
import org.jakstab.rtl.expressions.RTLOperation;
import org.jakstab.rtl.expressions.RTLSpecialExpression;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.expressions.RTLVariableIsOrdered;
import org.jakstab.rtl.expressions.Writable;
import org.jakstab.rtl.statements.DefaultStatementVisitor;
import org.jakstab.rtl.statements.RTLAlloc;
import org.jakstab.rtl.statements.RTLAssume;
import org.jakstab.rtl.statements.RTLDealloc;
import org.jakstab.rtl.statements.RTLHavoc;
import org.jakstab.rtl.statements.RTLMemcpy;
import org.jakstab.rtl.statements.RTLMemoryAssignment;
import org.jakstab.rtl.statements.RTLMemset;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.rtl.statements.RTLUnknownProcedureCall;
import org.jakstab.rtl.statements.RTLVariableAssignment;
import org.jakstab.rtl.Context;
import org.jakstab.util.Characters;
import org.jakstab.util.FastSet;
import org.jakstab.util.MapMap.EntryIterator;
import org.jakstab.util.Sets;
import org.jakstab.util.Tuple;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import java.util.Arrays;
import java.math.BigInteger;
import java.math.BigDecimal;
import java.util.TreeMap;

import cc.sven.bdd.*;
import cc.sven.constraint.*;
import cc.sven.tlike.*;
import cc.sven.equivalences.*;
import scala.math.BigInt;

public class BDDState implements AbstractState {

	private static final int WIDEN_PREC_INIT = 64;
	private static final int SLOW_WIDEN_INIT = 0;
	//evidences for Scala type classes
	private static MemoryRegionIsOrdered memoryRegionIsOrdered = new MemoryRegionIsOrdered();
	private static RTLNumberIsOrdered rtlNumberIsOrdered = new RTLNumberIsOrdered();
	private static RTLVariableIsOrdered rtlVariableIsOrdered = new RTLVariableIsOrdered();
	private static RTLNumberIsDynBounded rtlNumberIsDynBounded = new RTLNumberIsDynBounded();
	private static RTLNumberIsDynBoundedBits rtlNumberIsDynBoundedBits = new RTLNumberIsDynBoundedBits();
	private static RTLNumberToLongBWCaster rtlNumberToLongBWCaster = new RTLNumberToLongBWCaster();
	private static LongBWToRTLNumberCaster longBWToRTLNumberCaster = new LongBWToRTLNumberCaster();

	private BDDState(BDDVariableValuation vartable, PartitionedMemory<BDDSet> memtable, AllocationCounter counter, Equivalences<MemoryRegion, RTLNumber, RTLVariable> eqs,
			Map<RTLVariable, Pair<Integer, Integer>> widenVarTable, Map<Pair<MemoryRegion, Long>, Integer>
			widenMemTable, Map<RTLVariable, CBDD> widenVarPrecisionTreeTable) {
		this.abstractVarTable = vartable;
		this.abstractMemoryTable = memtable;
		this.allocationCounter = counter;
		this.equivalences = eqs;
		this.widenVarTable = widenVarTable;
		this.widenMemTable = widenMemTable;
		this.widenVarPrecisionTreeTable = widenVarPrecisionTreeTable;
	}

	protected BDDState(BDDState proto) {
		this(new BDDVariableValuation(proto.abstractVarTable),
            new PartitionedMemory<BDDSet>(proto.abstractMemoryTable),
            AllocationCounter.create(),
            proto.equivalences, proto.widenVarTable, proto.widenMemTable, proto.widenVarPrecisionTreeTable);
	}

	public BDDState() {
		this(new BDDVariableValuation(new BDDSetFactory()),
			new PartitionedMemory<BDDSet>(new BDDSetFactory()),
			AllocationCounter.create(),
			Equivalences$.MODULE$.applyJ(memoryRegionIsOrdered, rtlNumberIsOrdered, rtlNumberIsDynBoundedBits, rtlVariableIsOrdered, rtlNumberToLongBWCaster),
			new HashMap<RTLVariable, Pair<Integer, Integer>>(),
			new HashMap<Pair<MemoryRegion, Long>, Integer>(), new HashMap<RTLVariable, CBDD>());
	}

	private final BDDVariableValuation abstractVarTable;
	private final PartitionedMemory<BDDSet> abstractMemoryTable;
	private final AllocationCounter allocationCounter;
	private Equivalences<MemoryRegion, RTLNumber, RTLVariable> equivalences;
    private final Map<RTLVariable, Pair<Integer, Integer>> widenVarTable;
    // private final TreeMap<Pair<MemoryRegion, Long>, Integer> widenMemTable;
    private final Map<Pair<MemoryRegion, Long>, Integer> widenMemTable;
    private Map<RTLVariable, CBDD> widenVarPrecisionTreeTable;

	private static Variable<MemoryRegion, RTLNumber, RTLVariable> variable(RTLVariable v) {
		return StorageEntity$.MODULE$.variableJ(v, memoryRegionIsOrdered, rtlNumberIsOrdered, rtlNumberIsDynBoundedBits, rtlVariableIsOrdered, rtlNumberToLongBWCaster);
	}
	private static MemLoc<MemoryRegion, RTLNumber, RTLVariable> memLoc(MemoryRegion r, RTLNumber a) {
		return StorageEntity$.MODULE$.memLoc(r, a, memoryRegionIsOrdered, rtlNumberIsOrdered, rtlNumberIsDynBoundedBits, rtlVariableIsOrdered, rtlNumberToLongBWCaster);
	}

	private static final Logger logger = Logger.getLogger(BDDState.class);

	/**
	 * Counts allocs at allocation sites 
	 */
	private static final class AllocationCounter {

		public static AllocationCounter create() {
			return new AllocationCounter();
		}

		public static AllocationCounter create(AllocationCounter proto) {
			return new AllocationCounter(proto.leaf);
		}

		private static final class AllocationTreeNode {
			private final Location location;
			private final AllocationTreeNode parent;
			public AllocationTreeNode(Location location, AllocationTreeNode parent) {
				this.location = location; this.parent = parent;
			}
		}

		private AllocationTreeNode leaf;

		private AllocationCounter(AllocationTreeNode leaf) {
			this.leaf = leaf;
		}

		private AllocationCounter() {
			this(null);
		}

		public int countAllocation(Location loc) {
			int count = 0;
			for (AllocationTreeNode iter = leaf; iter != null; iter = iter.parent)
				if (iter.location.equals(loc))
					count++;
			leaf = new AllocationTreeNode(loc, leaf);
			return count;
		}

		public AllocationCounter join(AllocationCounter other) {
			// TODO: Implement some kind of joining
			//throw new UnsupportedOperationException("Missing join implementation!");
			// This is invoked only for based constant propagation... don't know if this quick fix is correct?
			return this;
		}

	}

	@Override
	public String toString() {
		if(isTop()) return Characters.TOP;
		else if(isBot()) return Characters.BOT;
		else return "(Var = " + abstractVarTable.toString() + ", " + abstractMemoryTable.toString() + " | " + equivalences.toString() + ")";
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		BDDState that = (BDDState) l;
		if(this == that) return true;
		if(that.isTop() || isBot()) return true;
		if(isTop() || that.isBot()) return false;

		return abstractVarTable.lessOrEqual(that.abstractVarTable)
				&& abstractMemoryTable.lessOrEqual(that.abstractMemoryTable);
	}

	@Override
	public boolean isTop() {
		return abstractMemoryTable.isTop() && abstractVarTable.isTop();
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		logger.debug("projection from concretization for " + expressions.length + " expressions");
		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			BDDSet aValue = abstractEval(expressions[i]);
			//TODO SCM : fix - what if set is full for boolean?
			logger.debug("expression: " + expressions[i] + " evalutated to: "+ aValue + " "+ aValue.isTop());
			if(aValue.getSet().isFull()) {
				//is Boolean expression?
				if(expressions[i].getBitWidth() == 1)  {
					FastSet<RTLNumber> tmp = new FastSet<RTLNumber>(2);
					Collections.addAll(tmp, ExpressionFactory.TRUE, ExpressionFactory.FALSE);
					cValues.set(i, tmp);
				} else
					cValues.set(i, RTLNumber.ALL_NUMBERS);
			} else {
				//XXX limit up to k
				logger.debug("limit needed for: " + aValue + " with " + aValue.getSet().sizeBigInt() + " elements");
				cValues.set(i, aValue.concretize());
			}
		}
		//logger.debug(cValues);
		return Sets.crossProduct(cValues);
	}

	@Override
	public BDDState join(LatticeElement l) {
		BDDState that = (BDDState) l;

		if (isTop() || that.isBot()) return this;
		if (isBot() || that.isTop()) return that;

		BDDVariableValuation newVarVal = 
				abstractVarTable.join(that.abstractVarTable); 
		PartitionedMemory<BDDSet> newStore = 
				abstractMemoryTable.join(that.abstractMemoryTable);
		AllocationCounter newAllocCounters = 
				allocationCounter.join(that.allocationCounter);
		//TODO scm check bug: is join correctly handled with respect to bitwidth? check ordering on RTLNumbers! can we change it there (JavaOrdering[RTLNumber]) without any ill effects?
		Equivalences<MemoryRegion, RTLNumber, RTLVariable> newEquivalences =
				equivalences.intersect(that.equivalences);

        Map<RTLVariable, Pair<Integer, Integer>> joinedWidenVarTable = new HashMap<RTLVariable, Pair<Integer, Integer>>(widenVarTable);
        for (Map.Entry<RTLVariable, Pair<Integer, Integer>> entry : that.widenVarTable.entrySet()) {
            RTLVariable key = entry.getKey();
            Pair<Integer, Integer> val = entry.getValue();
            if (!joinedWidenVarTable.containsKey(key)) {
                joinedWidenVarTable.put(key, val);
            } else { // use smaller precision
                if (val.getLeft() < widenVarTable.get(key).getLeft()) joinedWidenVarTable.replace(key, val);
            }
        }

        HashMap<Pair<MemoryRegion, Long>, Integer> joinedWidenMemTable = new HashMap<Pair<MemoryRegion, Long>, Integer>
                (widenMemTable); // shallow copy current
        for (Map.Entry<Pair<MemoryRegion, Long>, Integer> entry : that.widenMemTable.entrySet()) {
            Pair<MemoryRegion, Long> key = entry.getKey();
            int val = entry.getValue();
            if (!joinedWidenMemTable.containsKey(key)) {
                joinedWidenMemTable.put(key, val);
            } else {
                if (val < widenMemTable.get(key)) joinedWidenMemTable.replace(key, val);
            }
        }

        Map<RTLVariable, CBDD> joinedWVPTT = new HashMap<RTLVariable, CBDD>(widenVarPrecisionTreeTable);
        for(Map.Entry<RTLVariable, CBDD> entry : that.widenVarPrecisionTreeTable.entrySet()) {
            RTLVariable key = entry.getKey();
            CBDD val = entry.getValue();
            if (!joinedWVPTT.containsKey(key)) {
                joinedWVPTT.put(key, val);
            } else {
                joinedWVPTT.put(key, val.$amp$amp(joinedWVPTT.get(key)));
            } // TODO make sure this works
        }
        return new BDDState(newVarVal, newStore, newAllocCounters, newEquivalences, joinedWidenVarTable, joinedWidenMemTable,
                joinedWVPTT);
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
	}

	private Context getContext() {
		Context context = new Context();
		for(Map.Entry<RTLVariable, BDDSet> entry : abstractVarTable) {
			RTLVariable var = entry.getKey();
			BDDSet val = entry.getValue();
			if(val.hasUniqueConcretization())
				context.addAssignment(var, val.getSet().randomElement());
		}
		return context;
	}

	@Override
	public String getIdentifier() {
		//return Long.toString(stateId);
		return Long.toString(hashCode());
	}

	@Override
	public boolean equals(Object obj) {
		if(!(obj instanceof BDDState)) return false;
		BDDState that = (BDDState) obj;
		if(this == that) return true;
		return abstractVarTable.equals(that.abstractVarTable) && abstractMemoryTable.equals(that.abstractMemoryTable);
	}
	/*None Interface Methods - called in BDDAddressTracking
	 * See BasedNumberValuation for similar structure.
	 */

	private void clearTemporaryVariables() {
		for(RTLVariable var : Program.getProgram().getArchitecture().getTemporaryVariables())
			abstractVarTable.setTop(var);
	}
	
	private BDDSet getValue(RTLVariable var) {
		return abstractVarTable.get(var);
	}
	
	private void setValue(RTLVariable var, BDDSet value) {
		abstractVarTable.set(var, value);
	}

	private void addEquivalence(RTLVariable v1, RTLVariable v2) {
		if(!v1.getName().startsWith("tmp") && !v2.getName().startsWith("tmp"))
            equivalences = equivalences.insert(variable(v1), variable(v2));
	}
	private void addEquivalence(RTLVariable v, MemoryRegion r, RTLNumber n) {
		if(!v.getName().startsWith("tmp"))
            equivalences = equivalences.insert(variable(v), memLoc(r, n));
	}
	private void addEquivalence(MemoryRegion r, RTLNumber n, RTLVariable v) {
		addEquivalence(v, r, n);
	}
	private void addEquivalence(MemoryRegion r1, RTLNumber n1, MemoryRegion r2, RTLNumber n2) {
		equivalences = equivalences.insert(memLoc(r1, n1), memLoc(r2, n2));
	}
	private void removeEquivalenceMemoryEquivalences() {
		equivalences = equivalences.removeAllMemLocs();
	}
	private void removeEquivalenceMemLoc(MemoryRegion r, RTLNumber n) {
		equivalences = equivalences.remove(memLoc(r, n));
	}
	private void removeEquivalenceVariable(RTLVariable v) {
		equivalences = equivalences.remove(variable(v));
	}

    /**
     * REWRITE
     *
     * (C) Felix Lublow
     * @param other the other state
     * @return BDDState resulting from widening
     */
    public BDDState widen(BDDState other) {
        BDDState result = new BDDState(this);
        // variable table
        for (Map.Entry<RTLVariable, BDDSet> entry : abstractVarTable) {
            RTLVariable key = entry.getKey();
            BDDSet value = entry.getValue();
            BDDSet otherValue = other.abstractVarTable.get(key);
            if (!widenVarTable.containsKey(key)) { // create entry for widening info if not yet existent
                widenVarTable.put(key, Pair.create(WIDEN_PREC_INIT, SLOW_WIDEN_INIT));
            }
            int widenPrec = widenVarTable.get(key).getLeft();
            int slowWiden = widenVarTable.get(key).getRight();
            if (otherValue == null) continue;
            if (!value.equals(otherValue)) { // widen only sets which changed
                logger.info(" - widening variable " + key + " that had value " + value + " because of " + otherValue);
                if (value.getRegion() != otherValue.getRegion()) { // set to top if not of same memory region (?)
                    logger.info("!!!!!!!!!!!!!!!!!!!!!!!!!!!!!");
                    result.abstractVarTable.setTop(key); // TODO can this even happen for vars?
                } else { // else widen
                    // result.abstractVarTable.setTop(key); RELIC
                    // if precision larger than depth of either CBDD, set precision to greater of the two depths
                    int oldWidenPrec = widenPrec;
                    int valDepth = value.getSet().set().cbdd().depth();
                    int otherValDepth = otherValue.getSet().set().cbdd().depth();
                    logger.info(" - - prec.: " + widenPrec + ", depths " + valDepth + ", " + otherValDepth);
                    //if (widenPrec > valDepth && widenPrec > otherValDepth) { // TODO does this ever happen? rm?
                    //    widenPrec = (valDepth > otherValDepth) ? valDepth : otherValDepth;
                    //    logger.info("!!!!! set precision " + oldWidenPrec + " -> " + widenPrec + " because of
                    // depths " +
                    //            valDepth + ", " + otherValDepth);
                    //} // I believe I don't want this

                    if(!widenVarPrecisionTreeTable.containsKey(key)) {
                        widenVarPrecisionTreeTable.put(key, False$.MODULE$);
                    }
                    CBDD widenVarPrecisionTree = widenVarPrecisionTreeTable.get(key);
                    logger.info(" ~ precisionTree before update: " + widenVarPrecisionTree);
                    widenVarPrecisionTree = widenVarPrecisionTree.update_precisionTree(value.getSet().set().cbdd(),
                            otherValue.getSet().set().cbdd());
                    widenVarPrecisionTreeTable.put(key, widenVarPrecisionTree);
                    logger.info(" ~ precisionTree after update: " + widenVarPrecisionTree);
                    BDDSet tmp = new BDDSet(value.getSet().widen_precisionTree(otherValue.getSet(),
                            widenVarPrecisionTree), value.getRegion());

                    logger.info(" - variable widen result: " + tmp);
                    BigInt diff = tmp.getSet().sizeBigInt().$minus(otherValue.getSet().sizeBigInt());
                    //if(diff.$less(new BigInt(BigInteger.valueOf(widenPrec)))){
                    // TODO consider removing difference conditional and instead constantly loosen precision
                    int smallestDepthPrec = (valDepth < otherValDepth) ? valDepth : otherValDepth;
                    if (widenPrec < smallestDepthPrec) smallestDepthPrec = widenPrec;
                    if (diff.$less(new BigInt(new BigDecimal((Math.pow(2, 64 - smallestDepthPrec) + 1) /*+ 1.0*/)
                            .toBigInteger()))) {
                        logger.info(" - slow widening cond. met: diff (" + diff + " [ = " + tmp.getSet().sizeBigInt
                                () + " - " + otherValue.getSet().sizeBigInt() + "]) < " + new BigInt(new BigDecimal(
                                (Math
                                        .pow(2, 64 - smallestDepthPrec) + 1)).toBigInteger()) + " [ = 2^(64 - " + smallestDepthPrec + ") + 1]");
                        // logger.info(" - slow widening cond. met: diff (" + diff +  " [ = " + tmp.getSet().sizeBigInt
                        // 		() + " - " + otherValue.getSet().sizeBigInt() + "]) " + "< prec " + widenPrec);
                        logger.info(" - - slowWiden: " + slowWiden);
                        if (slowWiden < 2) slowWiden++;
                        // else logger.info(" + slowWiden capped.");
                        if (widenPrec > 3) widenPrec = widenPrec - (2 + slowWiden);
                        else if (widenPrec > 2 && slowWiden < 1) widenPrec = widenPrec - 2;
                        else widenPrec = 0;
                    } else {
                        logger.info(" + widening fast enough: diff (" + diff + " [ = " + tmp.getSet().sizeBigInt() +
                                " - " + value.getSet().sizeBigInt() + "]) < " + new BigInt(new BigDecimal((Math.pow
                                (2, 64 - widenPrec) + 1)).toBigInteger()) + " [ = 2^(64 - " + smallestDepthPrec + ") + 1]");
                        widenPrec--;
                        slowWiden = SLOW_WIDEN_INIT;
                    }
                    result.widenVarTable.replace(key, Pair.create(widenPrec, slowWiden));
                    result.abstractVarTable.set(key, tmp);
                }
            }
        }

        // memory table
        for (EntryIterator<MemoryRegion, Long, BDDSet> iter = abstractMemoryTable.entryIterator(); iter.hasEntry(); iter.next()) {
            MemoryRegion region = iter.getLeftKey();
            Long offset = iter.getRightKey();
            Pair<MemoryRegion, Long> key = Pair.create(region, offset);
            BDDSet value = iter.getValue();
            BDDSet otherValue = other.abstractMemoryTable.get(region, offset, value.getBitWidth());
            if (!widenMemTable.containsKey(key)) { // create entry for widening info if not yet existent
                widenMemTable.put(key, WIDEN_PREC_INIT);
            }
            int widenPrec = widenMemTable.get(key);
            if (otherValue == null) continue;
            if (!value.equals(otherValue)) {
                logger.info(" - widening memory cell (" + region + " | " + value.getBitWidth() + " | " + offset + ") " +
                        "that had value " + value + " because of " + otherValue);
                if (value.getRegion() != otherValue.getRegion()) { // set to top if not of same memory region (?)
                    logger.info(" * setting to top: old " + value + ", new " + otherValue);
                    result.abstractMemoryTable.set(region, offset, value.getBitWidth(), BDDSet.topBW(value.getBitWidth()));
                } else { // else widen
                    // result.abstractMemoryTable.set(region, offset, value.getBitWidth(), BDDSet.topBW(value.getBitWidth()));
                    int oldWidenPrec = widenPrec;
                    int valDepth = value.getSet().set().cbdd().depth();
                    int otherValDepth = otherValue.getSet().set().cbdd().depth();
                    logger.info(" * * prec.: " + widenPrec + ", depths " + valDepth + ", " + otherValDepth);
                    // if (widenPrec > valDepth && widenPrec > otherValDepth) {
                    //    widenPrec = (valDepth > otherValDepth) ? valDepth : otherValDepth;
                    //    logger.info("!!!!! set precision " + oldWidenPrec + " -> " + widenPrec + " because of
                    // depths " +
                    //            valDepth + ", " + otherValDepth);
                    //}

                    BDDSet tmp = new BDDSet(value.getSet().widen_naive(otherValue.getSet(), widenPrec), region);
                    logger.info(" * memory widen result: " + tmp);

                    BigInt diff = tmp.getSet().sizeBigInt().$minus(otherValue.getSet().sizeBigInt());
                    // TODO consider removing difference conditional and instead constantly loosen precision
                    int smallestDepthPrec = (valDepth < otherValDepth) ? valDepth : otherValDepth;
                    if (widenPrec < smallestDepthPrec) smallestDepthPrec = widenPrec;
                    if (diff.$less(new BigInt(new BigDecimal((Math.pow(2, 64 - smallestDepthPrec) + 1))
                            .toBigInteger()))) {
                        logger.info(" * slow widening cond. met: diff (" + diff + " [ = " + tmp.getSet().sizeBigInt
                                () + " - " + otherValue.getSet().sizeBigInt() + "]) < " + new BigInt(new BigDecimal(
                                (Math
                                        .pow(2, 64 - smallestDepthPrec) + 1)).toBigInteger()) + " [ = 2^(64 - " + smallestDepthPrec + ") + 1]");
                        if (widenPrec > 1) widenPrec = widenPrec - 2;
                        else widenPrec = 0;
                    } else {

                        logger.info(" * widening fast enough: diff (" + diff + " [ = " + tmp.getSet().sizeBigInt() +
                                " - " + value.getSet().sizeBigInt() + "]) < " + new BigInt(new BigDecimal((Math.pow
                                (2, 64 - widenPrec) + 1)).toBigInteger()) + " [ = 2^(64 - " + smallestDepthPrec + ") + 1]");
                        widenPrec--;
                    }

                    result.widenMemTable.replace(key, widenPrec);
                    result.abstractMemoryTable.set(region, offset, value.getBitWidth(), tmp);

                }
            }
        }

        return result;
    }
	/*private void setValue(RTLVariable var, BDDSet value, ExplicitPrecision eprec) {
		BDDSet valueToSet;
		switch(eprec.getTrackingLevel(var)) {
		case NONE:
			logger.debug("Precision prevents value " + value + " to be set for " + var);
			valueToSet = BDDSet.topBW(var.getBitWidth());
			break;
		case REGION:
			logger.debug("Precision created ANYNUM for " + var);
			valueToSet = new BDDSet(BDDSet.topBW(var.getBitWidth()).getSet(), value.getRegion());
			break;
		case FULL:
		default:
			valueToSet = value;
		}
		abstractVarTable.set(var, valueToSet);
	}*/
	
	/* TODO SCM check!
	void setValue(RTLVariable var, BasedNumberElement value, ExplicitPrecision precision) {
		BasedNumberElement valueToSet;
		switch (precision.getTrackingLevel(var)) {
		case NONE:
			logger.debug("Precision prevents value " + value + " to be set for " + var);
			valueToSet = BasedNumberElement.getTop(var.getBitWidth());
			break;
		case REGION:
			valueToSet = new BasedNumberElement(value.getRegion(), 
					NumberElement.getTop(var.getBitWidth()));
			break;
		default:
			valueToSet = value;
		}
		aVarVal.set(var, valueToSet);
	}
	 */
	
	// Returns true if set was successful, false if memory was overapproximated or location was not a singleton
	private boolean setMemoryValue(BDDSet pointer, int bitWidth, BDDSet value) {
		if(pointer.isTop()) {
			abstractMemoryTable.setTop();
			return false;
		} else if(pointer.getSet().isFull()) {
			abstractMemoryTable.setTop(pointer.getRegion());
			return false;
		} else {
			MemoryRegion region = pointer.getRegion();
			if(pointer.getSet().sizeGreaterThan(100*BDDTracking.threshold.getValue())) {
				logger.info("Overapproximating large setMemory access: " + pointer + " value: "+ value  );
				abstractMemoryTable.setTop(pointer.getRegion());
				return false;
			}
			for(RTLNumber rtlnum : pointer.concretize()) {
				// XXX SCM why the bitWidth - is contained in rtlnum and in BDDSet.singleton... - CHECK!
				abstractMemoryTable.set(region, rtlnum.longValue(), bitWidth, value);
			}
			return pointer.isSingleton();
		}
	}

	private BDDSet getMemoryValue(BDDSet pointer, int bitWidth) {
		//XXX like in the original - if pointer.getRegion() == MemoryRegion.TOP -> assert false...
		logger.verbose("memory access for: " + pointer + " bw: " + bitWidth);
		if(pointer.isTop() || pointer.getSet().isFull())
			return BDDSet.topBW(bitWidth);
		if(pointer.getRegion() == MemoryRegion.TOP)
		{
			logger.error("Pointer deref with TOP region (pointer: " + pointer +")");
			return BDDSet.topBW(bitWidth);
		}
		if(pointer.getSet().sizeGreaterThan(100*BDDTracking.threshold.getValue())) {
			logger.info("Overapproximating large getMemory access: " + pointer );
			return BDDSet.topBW(bitWidth);
		}
		//the following is again essentially a fold1...
		BDDSet result = null;
		for(RTLNumber rtlnum : pointer.concretize()) {
			//logger.debug("accessing at: " + pointer.getRegion() + ", " + rtlnum.intValue());
			BDDSet values = abstractMemoryTable.get(pointer.getRegion(), rtlnum.intValue(), bitWidth);
			if(result == null)
				result = BDDSet.empty(values.getBitWidth(), values.getRegion());
			assert values.getBitWidth() == result.getBitWidth() : "Try to union different bitwidths at pointer deref";
			if(values.getRegion() != result.getRegion())
				return BDDSet.topBW(result.getBitWidth());
			result = new BDDSet(result.getSet().union(values.getSet()), result.getRegion());
		}
		logger.verbose("memory access result: " + result);
		return result;
	}

	private BDDSet abstractEvalAddress(RTLMemoryLocation m) {
		BDDSet abstractAddress = abstractEval(m.getAddress());
		//Segment register is some special x86 magic
		RTLExpression segmentReg = m.getSegmentRegister();
		if(segmentReg != null) {
			if(abstractAddress.getRegion() != MemoryRegion.GLOBAL)
				return BDDSet.topBW(m.getBitWidth());
			BDDSet segmentValue = abstractEval(segmentReg);
			// segment register handling
			//  - ok if segment is singleton of value 0
			if (segmentValue.isSingleton() && segmentValue.randomElement().intValue() == 0) {
				abstractAddress = new BDDSet(abstractAddress.getSet(), segmentValue.getRegion());
			} else {
				logger.warn("Segment " + segmentReg + " has been assigned a value!");
				abstractAddress = BDDSet.topBW(abstractAddress.getBitWidth());
			}
		}
		return abstractAddress;
	}

	BDDSet abstractEval(RTLExpression e) {
		ExpressionVisitor<BDDSet> visitor = new ExpressionVisitor<BDDSet>() {

			@Override
			public BDDSet visit(RTLBitRange e) {
				logger.debug("extracting bitrange: " + e);
				BDDSet abstractFirst = e.getFirstBitIndex().accept(this);
				BDDSet abstractLast = e.getLastBitIndex().accept(this);
				BDDSet abstractOperand = e.getOperand().accept(this);

				if(!(abstractFirst.hasUniqueConcretization() && abstractLast.hasUniqueConcretization()))
					return BDDSet.topBW(e.getBitWidth());
				RTLNumber loRTL = abstractFirst.randomElement();
				RTLNumber hiRTL = abstractLast.randomElement();
				long loLong = loRTL.longValue();
				long hiLong = hiRTL.longValue();
				int lo = loRTL.intValue();
				int hi = hiRTL.intValue();
				if(!((long) lo == loLong)
				|| !((long) hi == hiLong)
				|| !(lo >= 0)
				|| !(hi >= 0))
					return BDDSet.topBW(e.getBitWidth());
				BDDSet ret = abstractOperand.bitExtract(lo, hi);
				logger.debug("extracted: " + ret);
				return ret;
			}

			@Override
			public BDDSet visit(RTLConditionalExpression e) {
				BDDSet abstractCondition = e.getCondition().accept(this);
				logger.debug("abstr cond: " + abstractCondition);
				BDDSet result = BDDSet.empty(e.getBitWidth());
				if(BDDSet.TRUE.lessOrEqual(abstractCondition)) {
					logger.debug("true branch");
					BDDSet abstractTrue = e.getTrueExpression().accept(this);
					result = result.join(abstractTrue);
				}
				if(BDDSet.FALSE.lessOrEqual(abstractCondition)) {
					logger.debug("false branch");
					BDDSet abstractFalse = e.getFalseExpression().accept(this);
					result = result.join(abstractFalse);
				}
				return result;
			}

			@Override
			public BDDSet visit(RTLMemoryLocation m) {
				//XXX restrict to n values
				return getMemoryValue(abstractEvalAddress(m), m.getBitWidth());
			}

			@Override
			public BDDSet visit(RTLNondet e) {
				return BDDSet.topBW(e.getBitWidth());
			}

			@Override
			public BDDSet visit(RTLNumber e) {
				return BDDSet.singleton(e);
			}

			//This should actually be a function returning a triple. But I feel funny today and... JAVA...
			class CheckResult {
				private int bits;
				private MemoryRegion region;
				private boolean ok = true;
				public CheckResult(RTLOperation e, BDDSet[] abstractOperands) {
					assert e.getOperandCount() > 0 : "Check failure for 0 operands";
					this.region = abstractOperands[0].getRegion();
					this.bits = abstractOperands[0].getBitWidth();
					logger.debug("expression "+e+" # operands:" + e.getOperandCount());
					logger.debug("operand: " + abstractOperands[0]);
					for(int i = 1; i < e.getOperandCount(); i++) {
						logger.debug("operand: " + abstractOperands[i]);
						/*if(this.region == MemoryRegion.TOP
								|| abstractOperands[i].getRegion() == MemoryRegion.TOP) {
							this.region = MemoryRegion.TOP;
							break;
						}*/
						if(this.region == MemoryRegion.GLOBAL)
							this.region = abstractOperands[i].getRegion();
						if(abstractOperands[i].getRegion() == MemoryRegion.TOP) {
							this.ok = false;
							this.region = MemoryRegion.TOP;
							logger.debug("Check for Region == TOP for " + abstractOperands[i]);
							break;
						} else if((abstractOperands[i].getRegion() != MemoryRegion.GLOBAL
								&& this.region != abstractOperands[i].getRegion())
								|| this.bits != abstractOperands[i].getBitWidth()) {
							logger.debug("Check for Region or BitWidth failed: this.region: " + this.region + ", that.region: " + abstractOperands[i].getRegion() + ", this.bits: " + this.bits + ", that.bits: " + abstractOperands[i].getBitWidth());
							this.ok = false;
							break;
						}
					}
				}
				public boolean getOk() { return ok; }
				public boolean getTop() { return this.region == MemoryRegion.TOP; }
				public MemoryRegion getRegion() {
					assert getOk();
					return region;
				}
				public int getBitWidth() {
					assert getOk();
					return bits;
				}
			}

			@Override
			public BDDSet visit(RTLOperation e) {
				BDDSet[] abstractOperands = new BDDSet[e.getOperandCount()];

				for(int i = 0; i < e.getOperandCount(); i++) {
					abstractOperands[i] = e.getOperands()[i].accept(this);
					if(abstractOperands[i].getSet().isEmpty()) {
						logger.error("found EMPTY Set for op #"+i+" in operation: "+e);
					}
				}

				BDDSet op0;
				BDDSet op1;
				BDDSet op2;
				CheckResult check;
				
				try {
					logger.debug("processing: " + e + " operator: " + e.getOperator());
				switch(e.getOperator()) {
				/* decided to go for code duplication for readability (more separate cases).
				 * also, clone researchers need something meaningful to analyze...
				 */
				case EQUAL:
					assert e.getOperandCount() == 2 : "EQUAL called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.getRegion() != MemoryRegion.GLOBAL
							&& !op0.isTop()
							&& op1.hasUniqueConcretization()
							&& op1.getSet().contains(ExpressionFactory.createNumber(0, op1.getBitWidth())))
						return BDDSet.FALSE;
					if(op1.getRegion() != MemoryRegion.GLOBAL
							&& !op1.isTop()
							&& op0.hasUniqueConcretization()
							&& op0.getSet().contains(ExpressionFactory.createNumber(0, op0.getBitWidth())))
						return BDDSet.FALSE;
					if(op0.isTop() || op1.isTop()) {
						return BDDSet.topBW(e.getBitWidth());
					} else {
						if( op0.getBitWidth() == op1.getBitWidth()) {
							if(op0.getRegion() == op1.getRegion()) {
								BDDSet result = BDDSet.empty(1);
								logger.debug("op0" + op0);
								logger.debug("op1" + op1);
								logger.debug(op0.getSet().intersect(op1.getSet()));
								if(!op0.getSet().intersect(op1.getSet()).isEmpty())
									result = result.join(BDDSet.TRUE);
								if(!op0.getSet().invert().intersect(op1.getSet()).isEmpty())
									result = result.join(BDDSet.FALSE);
								// XXX arne: i think this way round needs also be checked...
								if(!op0.getSet().intersect(op1.getSet().invert()).isEmpty())
									result = result.join(BDDSet.FALSE);
								assert !result.getSet().isEmpty() : "Equal"+e+" produced no result!?";
								return result;
							} else {
								logger.debug("EQUAL with differing regions: (" + op0 + " " + e.getOperator() + " " + op1 + ")");
								return BDDSet.topBW(e.getBitWidth());
							}
						}
					}
					assert false : "EQUAL called on something crazy: (" + op0 + " " + e.getOperator() + " " + op1 + ")";
					break;
				case UNSIGNED_LESS: // XXX [-SCM-] This SHOULD be a BUG . The order in UNSIGNED and signed operations are different!
					
				case LESS:
					assert e.getOperandCount() == 2 : "LESS or UNSIGNED_LESS called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.isTop() || op1.isTop()) {
						// TODO: handle: non-TOP operand could be max element which would result in constant false
						return BDDSet.topBW(e.getBitWidth());
					} else {
						if(!op0.getSet().isEmpty()
							&& !op1.getSet().isEmpty()
							&& op0.getBitWidth() == op1.getBitWidth()) {
							if(op0.getRegion() == op1.getRegion()) {
								BDDSet result = BDDSet.empty(1);
								if(op0.getSet().min().longValue() < op1.getSet().max().longValue())
									result = result.join(BDDSet.TRUE);
								if(op0.getSet().max().longValue() >= op1.getSet().min().longValue())
									result = result.join(BDDSet.FALSE);
								return result;
							} else {
								logger.debug("LESS with differing regions: (" + op0 + " " + e.getOperator() + " " + op1 + ")");
								return BDDSet.topBW(e.getBitWidth());
							}
						}
					}
					assert false : "LESS called on something crazy: (" + op0 + " " + e.getOperator() + " " + op1 + ")";
					break;
				case UNSIGNED_LESS_OR_EQUAL: // XXX [-SCM-] This SHOULD be a BUG . The order in UNSIGNED and signed operations are different!
				case LESS_OR_EQUAL:
					assert e.getOperandCount() == 2 : "UNSIGNED_LESS_OR_EQUAL or LESS_OR_EQUAL called with " + e.getOperandCount() + " operands";
					//== and <
					RTLExpression eLess = ExpressionFactory.createLessThan(e.getOperands()[0], e.getOperands()[1]);
					RTLExpression eEqual = ExpressionFactory.createEqual(e.getOperands()[0], e.getOperands()[1]);
					BDDSet less = eLess.accept(this);
					BDDSet equal = eEqual.accept(this);
					return less.join(equal);
				case NOT:
					assert e.getOperandCount() == 1 : "NOT called with " + e.getOperandCount() + " operands";
			//		logger.debug(abstractOperands[0]);
					return new BDDSet(abstractOperands[0].getSet().bNot());
				case NEG:
					assert e.getOperandCount() == 1 : "NEG called with " + e.getOperandCount() + " operands";
			//		logger.debug(abstractOperands[0]);
					return new BDDSet(abstractOperands[0].getSet().negate());
				case AND:
					check = new CheckResult(e, abstractOperands);
					if(check.getTop()) {
						if(e.getOperandCount()==2 && abstractOperands[0].isTop() && abstractOperands[1].hasUniqueConcretization()) {
							IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
							return new BDDSet(res.bAnd(abstractOperands[1].getSet()),MemoryRegion.GLOBAL);
						}
						logger.debug("abstractEval(" + e + ") == TOP on State: " + BDDState.this);
						return BDDSet.topBW(e.getBitWidth());
					} else if(check.getOk()) {
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
						for(int i = 1; i < e.getOperandCount(); i++)
							res = res.bAnd(abstractOperands[i].getSet());
						return new BDDSet(res, check.getRegion());
					}
					assert false : "AND called on something crazy";
					break;
				case OR:
					check = new CheckResult(e, abstractOperands);
					if(check.getTop()) {
						logger.debug("abstractEval(" + e + ") == TOP on State: " + BDDState.this);
						return BDDSet.topBW(e.getBitWidth());
					} else if(check.getOk()) {
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
				//		logger.debug("base operand: "+ res + (abstractOperands[0].getSet().isFull()?" [full]":"[]"));
						for(int i = 1; i < e.getOperandCount(); i++) {
						//	logger.debug("next operand: "+ abstractOperands[i] + (abstractOperands[i].getSet().isFull()?" [full]":"[]"));
							//IntLikeSet<Long, RTLNumber> set = abstractOperands[i].getSet();
							//res = res.bOr(abstractOperands[i].getSet());
							res = abstractOperands[i].getSet().bOr(res);
						}
					//	logger.debug("evaluated OR");

					//	logger.debug("evaluated to full set: "+ res.isFull());
					//	logger.debug("evaluated to region: "+ check.getRegion());
					//	logger.debug("evaluated set of size: "+ res.sizeBigInt());
						return new BDDSet(res, check.getRegion());
					}
					assert false : "OR called on something crazy";
					break;
				case XOR:
					check = new CheckResult(e, abstractOperands);
					if(check.getTop()) {
						logger.debug("abstractEval(" + e + ") == TOP on State: " + BDDState.this);
						return BDDSet.topBW(e.getBitWidth());
					} else if(check.getOk()) {
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
						for(int i = 1; i < e.getOperandCount(); i++)
							res = res.bXOr(abstractOperands[i].getSet());
						return new BDDSet(res, check.getRegion());
					}
					assert false : "XOR called on something crazy";
					break;
				case PLUS:
					check = new CheckResult(e, abstractOperands);
					boolean allSame = true;
					for(int i = 1; i < e.getOperandCount() && allSame; i++)
						if(e.getOperands()[i] != e.getOperands()[0])
							allSame = false;
					if(allSame && (check.getTop() || check.getOk())
					&& (e.getOperandCount() & (e.getOperandCount() - 1)) == 0) { //check power of two operand count - can be lifted as soon as mulSingleton is there - then use mulSingleton instead of shift
						logger.debug("Special case for plus on same arguments, e.g. add %eax %eax.");
						//special case, e.g. add %eax %eax == 2 * %eax
						int toShift = 0;
						for(int ops = e.getOperandCount(); (ops & 1) == 0; ops >>= 1)
							toShift++;
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet().bShl(toShift);
						if(check.getOk())
							return new BDDSet(res, check.getRegion());
						else {
							//SCM this is Hacky - we do not know the region, really. But GLOBAL is as good a guess as any...
							logger.warn("We guessed a region in special case for add");
							return new BDDSet(res, MemoryRegion.GLOBAL);
						}
					} else if(check.getTop()) {
						logger.debug("abstractEval(" + e + ") == TOP on State: " + BDDState.this);
						return BDDSet.topBW(e.getBitWidth());
					} else if(check.getOk()) {
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
						for(int i = 1; i < e.getOperandCount(); i++)
							res = res.plus(abstractOperands[i].getSet());
						return new BDDSet(res, check.getRegion());
					}
					assert false : "PLUS called on something crazy";
					break;
				case SIGN_EXTEND:
					assert e.getOperandCount() == 3 : "SIGN_EXTEND called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					op2 = abstractOperands[2];
					if(op0.hasUniqueConcretization()
							&& op1.hasUniqueConcretization())
						return op2.signExtend(op0.randomElement().intValue(), op1.randomElement().intValue());
					assert false : "SIGN_EXTEND called on something crazy";
					break;
				case ZERO_FILL:
					assert e.getOperandCount() == 3 : "ZERO_FILL called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					op2 = abstractOperands[2];
					if(op0.hasUniqueConcretization()
							&& op1.hasUniqueConcretization())
						return op2.zeroFill(op0.randomElement().intValue(), op1.randomElement().intValue());
					assert false : "ZERO_FILL called on something crazy";
					break;
				case SHR:
					assert e.getOperandCount() == 2 : "SHR called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						// if op0 is top, use global as target region
						return new BDDSet(op0.getSet().bShr(op1.randomElement().intValue()),
								op0.isTop()?MemoryRegion.GLOBAL:op0.getRegion()); 
					assert false : "SHR called on something crazy";
					break;
				case SHL:
					assert e.getOperandCount() == 2 : "SHL called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bShl(op1.randomElement().intValue()), op0.getRegion());
					assert false : "SHL called on something crazy";
					break;
				case ROL:
					assert e.getOperandCount() == 2 : "ROL colled with " + e.getOperandCount() + "operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bRol(op1.randomElement().intValue()), op0.getRegion());
				case ROR:
					assert e.getOperandCount() == 2 : "ROR colled with " + e.getOperandCount() + "operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bRor(op1.randomElement().intValue()), op0.getRegion());
				case SAR:
					assert e.getOperandCount() == 2 : "SAR called with " + e.getOperandCount() + " operands";
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bSar(op1.randomElement().intValue()), op0.getRegion());
					assert false : "SAR called on something crazy";
					break;
				case MUL:
					check = new CheckResult(e, abstractOperands);
					//TODO scm remove
					final int prec = 5;
					final int maxk = 2*prec*BDDTracking.threshold.getValue();
					if(check.getTop()) {
						logger.debug("abstractEval(" + e + ") == TOP on State: " + BDDState.this);
						return BDDSet.topBW(e.getBitWidth());
					} else if(check.getOk()) {
						IntLikeSet<Long, RTLNumber> res = abstractOperands[0].getSet();
						for(int i = 1; i < e.getOperandCount(); i++) {
							//TODO SCM : in here, i must adjust bitwidth of res.
							IntLikeSet<Long, RTLNumber> op = abstractOperands[i].getSet();
							//XXX SCM the then branch should not have to exist - mul for up to maxk now does the same.
							/*if(!res.sizeGreaterThan(maxk) && !op.sizeGreaterThan(maxk)) {
								IntLikeSet<Long, RTLNumber> tmp = BDDSet.empty(check.getBitWidth() * 2, check.getRegion()).getSet();
								for(RTLNumber n1 : res.java())
									for(RTLNumber n2 : op.java()) {
										RTLExpression n1muln2 = ExpressionFactory.createMultiply(n1, n2).evaluate(new Context());
										assert n1muln2 instanceof RTLNumber : "No RTLNumber for result to multiplication!";
										//logger.info("adding a number... brace yourself! bitwidth of set : " + tmp.bits() + ", number: " + n1muln2.getBitWidth());
										tmp = tmp.add((RTLNumber) n1muln2);
									}
								res = tmp;
							} else {*/
								res = res.mul(maxk, prec, op);
							//}
						}
						logger.debug("MUL: " + res);
						return new BDDSet(res, check.getRegion());
					}
					assert false : "MUL called on something crazy";
					break;
				}
     			} catch (AssertionError f) {
     				logger.error("assertion failed while handling operation: " + e + " message: " + f.getMessage());
     				if(Options.failFast.getValue()) throw f;
     				return BDDSet.topBW(e.getBitWidth());
     			}
     
				logger.warn("XXX operator "+ e.getOperator() + " not handled in " + e);
				if(Options.debug.getValue()) assert false : "XXX operator "+ e.getOperator() + " not handled in " + e;
				return BDDSet.topBW(e.getBitWidth());
					/*
				case ROL:
				{
					BDDSet ret = BDDSet.topBW(e.getBitWidth());
					logger.debug("ROL not handled, returning: " + ret);
					return ret;
				}
				case ROR:
					assert false : "ROR not handled";
				break;
				case FSIZE:
				{
					BDDSet ret = BDDSet.topBW(e.getBitWidth());
					logger.debug("FSIZE not handled, returning: " + ret);
					return ret;
				}
				case FMUL:
					assert false : "FMUL not handled";
				break;
				case FDIV:
				{
					BDDSet ret = BDDSet.topBW(e.getBitWidth());
					logger.debug("FDIV not handled, returning: " + ret);
					return ret;
				}
				case DIV:
					assert false : "DIV not handled";
				break;
				case MOD:
					assert false : "MOD not handled";
				break;
				case POWER_OF:
					assert false : "POWER_OF not handled";
				break;
				case ROLC:
					assert false : "ROLC not handled";
				break;
				case RORC:
					assert false : "RORC not handled";
				break;
				case UNKNOWN:
					assert false : "UNKNOWN not handled";
				break;
				case CAST:
					assert false : "CAST not handled";
				break;
				default:
					assert false : "Operator not handled";
				break;
				}
				System.exit(1);
				//To make eclipse happy... Here you are, stupid.
				return null;*/
			}

			@Override
			public BDDSet visit(RTLSpecialExpression e) {
				//XXX todo [SCM] debug printf and possibly getprocaddress... - have a look at RTL definitions
				return BDDSet.topBW(e.getBitWidth());
			}

			@Override
			public BDDSet visit(RTLVariable e) {
				return abstractVarTable.get(e);
			}

		};

		BDDSet result = e.accept(visitor);

		logger.debug("abstractEval returned: " + result + " for: " + e);

		if(result.getSet().isEmpty()) {
			logger.error("found EMPTY Set as result for operation: "+e + " in state: "+ BDDState.this);
		}
		
		assert result.getBitWidth() == e.getBitWidth() : "Bitwidth changed from "+e.getBitWidth()+" to "+result.getBitWidth()+" during evaluation of " + e + " to " + result;
		return result;
	}


	public Set<AbstractState> abstractPost(final RTLStatement statement, final Precision precision) {
		logger.verbose("start processing abstractPost(" + statement + ") " + statement.getLabel());
		//final ExplicitPrecision eprec = (ExplicitPrecision)precision;
		Set<AbstractState> res = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {
			private final Set<AbstractState> thisState() {
				if(statement.getLabel() == null) logger.warn("No label: " + statement);
				if(!statement.getLabel().getAddress().equals(statement.getNextLabel().getAddress())) {
					BDDState post = new BDDState(BDDState.this);
					post.clearTemporaryVariables();
					return Collections.singleton((AbstractState) post);
				} else {
					return Collections.singleton((AbstractState) BDDState.this);
				}
			}

			private final BDDState copyThisState() {
				BDDState post = new BDDState(BDDState.this);
				if(statement.getNextLabel() == null
						|| !statement.getAddress().equals(statement.getNextLabel().getAddress())) {
					// New instruction
					post.clearTemporaryVariables();
				}
				return post;
			}

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				BDDState post = copyThisState();

				RTLVariable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				BDDSet evaledRhs = abstractEval(rhs);

				//TODO scm improve using equivalence information (a may remain if a = rhs)
				post.removeEquivalenceVariable(lhs);
				logger.debug("equivalence: removed for variable " + lhs + " from " + post + " with result " + post);

				if(rhs instanceof RTLVariable) {
					RTLVariable rhsVar = (RTLVariable) rhs;
					logger.debug("equivalence found: " + lhs + " = " + rhsVar);
					post.addEquivalence(lhs, rhsVar);
					logger.debug("equivalence result: " + post);
				} else if(rhs instanceof RTLMemoryLocation) {
					RTLMemoryLocation rhsMem = (RTLMemoryLocation) rhs;
					//TODO FIX scm this causes double evaluation probably
					BDDSet rhsAddress = abstractEvalAddress(rhsMem);
					if(rhsAddress.isSingleton()) {
						post.addEquivalence(lhs, rhsAddress.getRegion(), rhsAddress.randomElement());
						logger.debug("equivalence found: " + lhs + " = " + rhsMem + "(" + evaledRhs + ") result: " + post);
					} else {
						logger.debug("equivalence NOT found (no concrete rhsAddress): " + rhsMem + "(" + rhsAddress + ")");
					}
				} else {
                    logger.debug("equivalence NOT found (rhs not RTLVariable or RTLMemoryLocation)");
                }

				assert!evaledRhs.getSet().isEmpty();
				logger.debug("assigning "+ lhs + " to " + rhs);
				// Check for stackpointer alignment assignments (workaround for gcc compiled files)
				RTLVariable sp = Program.getProgram().getArchitecture().stackPointer();
				if (lhs.equals(sp) && rhs instanceof RTLOperation) {
					RTLOperation op = (RTLOperation)rhs;
					if (op.getOperator().equals(Operator.AND) && 
							op.getOperands()[0].equals(sp) &&
							op.getOperands()[1] instanceof RTLNumber) {
						evaledRhs = getValue(sp);
						logger.warn("Ignoring stackpointer alignment at " + stmt.getAddress());
					}
				}				
				logger.debug("assigning TOP: "+ evaledRhs.isTop());
				logger.debug("assigning full set: "+ evaledRhs.getSet().isFull());
				logger.debug("assigning EMPTY set: "+ evaledRhs.getSet().isEmpty());
				assert!evaledRhs.getSet().isEmpty();
				logger.debug("assigning region: "+ evaledRhs.getRegion());
				post.setValue(lhs, evaledRhs);
				logger.debug("completed assigning "+ lhs + " to " + evaledRhs);
				return Collections.singleton((AbstractState) post);
			}

			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				BDDState post = copyThisState();
				RTLExpression rhs = stmt.getRightHandSide();
				BDDSet evaledRhs = abstractEval(rhs);

				RTLMemoryLocation m = stmt.getLeftHandSide();
				BDDSet abstractAddress = abstractEvalAddress(m);

				//TODO scm improve using equivalence information (a may remain if a = rhs)
				logger.debug("equivalence: will operate on " + stmt);
				if(abstractAddress.getSet().sizeGreaterThan(1000)) {
					logger.debug("equivalence: address set too big -> removing all memory equivalences");
					post.removeEquivalenceMemoryEquivalences();
				} else {
					for(Iterator<RTLNumber> it = abstractAddress.getSet().javaIterator(); it.hasNext();) {
						RTLNumber n = it.next();
						logger.debug("equivalence: removing for address " + n);
						post.removeEquivalenceMemLoc(abstractAddress.getRegion(), n);
					}
				}

				if(abstractAddress.isSingleton()) {
					if(rhs instanceof RTLVariable) {
						RTLVariable rhsVar = (RTLVariable) rhs;
						post.addEquivalence(abstractAddress.getRegion(), abstractAddress.randomElement(), rhsVar);
						logger.debug("equivalence found: " + m + "(" + abstractAddress + ") = " + rhsVar + " result: " + post);
					} else if(rhs instanceof RTLMemoryLocation) {
						RTLMemoryLocation rhsMem = (RTLMemoryLocation) rhs;
						//TODO FIX scm this causes double evaluation probably
						BDDSet rhsAddress = abstractEvalAddress(rhsMem);
						if(rhsAddress.isSingleton()) {
							post.addEquivalence(abstractAddress.getRegion(), abstractAddress.randomElement(), rhsAddress.getRegion(), rhsAddress.randomElement());
							logger.debug("equivalence found: " + m + "(" + abstractAddress + ") = " + rhsMem + "(" + rhsAddress + ") result: " + post);
						} else {
							logger.debug("equivalence NOT found (no concrete rhsAddress): " + rhsMem + "(" + rhsAddress + ")");
						}
					} else {
						logger.debug("equivalence NOT found (rhs not RTLVariable or RTLMemoryLocation)");
					}
				} else {
					logger.debug("equivalence NOT found (no concrete lhs): "  + m + "(" + abstractAddress + ")");
				}

				if(!post.setMemoryValue(abstractAddress, m.getBitWidth(), evaledRhs)) {
					logger.verbose(stmt.getLabel() + ": Cannot precisely resolve memory write to " + m + ".");
					logger.debug("State: " + BDDState.this);
				}

				return Collections.singleton((AbstractState) post);
			}
			
			class TranslationState {
				private HashMap<Integer, RTLExpression> backMap;
				private HashMap<RTLExpression, Integer> expToMap;
				private HashMap<Integer, IntLikeSet<Long, RTLNumber>> valueMap;
				private HashMap<Integer, MemoryRegion> regionMap;
				private int counter;
				public TranslationState(HashMap<Integer, RTLExpression> bm, HashMap<RTLExpression, Integer> em, HashMap<RTLMemoryLocation, Integer> mm, HashMap<Integer, IntLikeSet<Long, RTLNumber>> values, HashMap<Integer, MemoryRegion> regions, int c) {
					this.backMap = bm;
					this.expToMap = em;
					this.valueMap = values;
					this.regionMap = regions;
					this.counter = c;
				}
				public TranslationState() {
					this.backMap = new HashMap<Integer, RTLExpression>();
					this.expToMap = new HashMap<RTLExpression, Integer>();
					this.valueMap = new HashMap<Integer, IntLikeSet<Long, RTLNumber>>();
					this.regionMap = new HashMap<Integer, MemoryRegion>();
					this.counter = 0;
				}
				public int freshId() {
					int res = counter;
					counter += 1;
					return res;
				}
				public HashMap<Integer, RTLExpression> getBackMap() { return backMap; }
				public HashMap<RTLExpression, Integer> getExpToMap() { return expToMap; }
				public HashMap<Integer, IntLikeSet<Long, RTLNumber>> getValueMap() { return valueMap; }
				public HashMap<Integer, MemoryRegion> getRegionMap() { return regionMap; }
				private MemoryRegion reduceRegion(FastSet<MemoryRegion> regions) {
					//fold1
					MemoryRegion result = MemoryRegion.TOP;
					for(MemoryRegion r : regions) {
						if(result.isTop() || result == r)
							result = r;
						else if(!r.isTop())
							result = MemoryRegion.TOP;
					}
					return result;
				}
				private BDDSet expToValue(RTLExpression op) {
					if(op instanceof RTLVariable)
						return BDDState.this.getValue((RTLVariable) op);
					else if(op instanceof RTLMemoryLocation) {
						BDDSet addresses = BDDState.this.abstractEval(((RTLMemoryLocation) op).getAddress());
						return getMemoryValue(addresses, op.getBitWidth());
					} else if(op instanceof RTLNumber)
						return BDDSet.singleton((RTLNumber) op);
					else
						return BDDSet.topBW(op.getBitWidth());
				}
				private void putValue(int k, BDDSet v, MemoryRegion region) { 
					//set must be the same if looked up twice - therefore update is ok
					valueMap.put(k, v.getSet());
					//region must be set to new "joined" region
					regionMap.put(k, region);
				}
				private int getId(RTLExpression forWhat) {
					if(forWhat instanceof RTLNumber)
						return freshId();
					Integer id = getExpToMap().get(forWhat);
					if(id == null) {
						id = freshId();
						expToMap.put(forWhat, id);
						backMap.put(id, forWhat);
					}
					return id;
				}
				public List<Integer> addOperandGroup(List<RTLExpression> ops) {
					//Pair<RTLExpression, BDDSet>[] values = new Pair<RTLExpression, BDDSet>[ops.length]; does not work for some reason
					//want map function...
					ArrayList<Pair<BDDSet, Integer>> values = new ArrayList<Pair<BDDSet, Integer>>(ops.size());
					FastSet<MemoryRegion> regions = new FastSet<MemoryRegion>();
					for(RTLExpression op : ops) {
						BDDSet value = expToValue(op);
						int id = getId(op);
						MemoryRegion knownRegion = getRegionMap().get(id);
						if(knownRegion != null)
							regions.add(knownRegion);
						regions.add(value.getRegion());
						values.add(new Pair<BDDSet, Integer>(value, id));
					}
					MemoryRegion region = reduceRegion(regions);
					ArrayList<Integer> ids = new ArrayList<Integer>(values.size());
					for(Pair<BDDSet, Integer> pair : values) {
						putValue(pair.getRight(), pair.getLeft(), region);
						ids.add(pair.getRight());
					}
					return ids;
				}
				@Override
				public String toString() {
					return "(BackMap: " + backMap + ", RegionMap: " + regionMap + ", ValueMap: " + valueMap + ")";
				}
			}
			
			private RTLExpression convertBoolean(RTLExpression exp) {
				if(exp instanceof RTLVariable && ((RTLVariable) exp).getBitWidth() == 1)
					return ExpressionFactory.createEqual(exp, ExpressionFactory.TRUE);
				return exp;
			}
			
			private boolean specialCaseBAndSingleton(RTLExpression exp) {
				if(exp instanceof RTLOperation) {
					RTLOperation op = (RTLOperation) exp;
					if(op.getOperator() == Operator.AND
							&& op.getOperandCount() == 2) {
						RTLExpression ex1 = op.getOperands()[0];
						RTLExpression ex2 = op.getOperands()[1];
						//one singleton, one variable
						//XXX also allow memory Access?
						//XXX also allow proper singleton (instead of just RTLNumber)?
						boolean res = (ex1 instanceof RTLNumber && ex2 instanceof RTLVariable) || (ex2 instanceof RTLNumber && ex1 instanceof RTLVariable);
						if(res)
							logger.debug("Constraint System: Hit special case for bitwise and singleton: " + exp);
						return res;
					}
				}
				return false;
			}
			
			private boolean specialCaseAddSingleton(RTLExpression exp) {
				if(exp instanceof RTLOperation) {
					RTLOperation op = (RTLOperation) exp;
					if(op.getOperator() == Operator.PLUS
							&& op.getOperandCount() == 2) {
						RTLExpression ex1 = op.getOperands()[0];
						RTLExpression ex2 = op.getOperands()[1];
						//one singleton, one variable
						//XXX also allow memory Access?
						//XXX also allow proper singleton (instead of just RTLNumber)?
						boolean res = (ex1 instanceof RTLNumber && ex2 instanceof RTLVariable) || (ex2 instanceof RTLNumber && ex1 instanceof RTLVariable);
						if(res)
							logger.debug("Constrint System: Hit special case for plus and singleton: " + exp);
						return res;
					}
				}
				return false;
			}
			
			private boolean rtlExpOkForRelOp(RTLExpression exp) {
				return exp instanceof RTLVariable
					|| exp instanceof RTLMemoryLocation
					|| exp instanceof RTLNumber
					//Special cases:
					|| specialCaseBAndSingleton(exp)
					|| specialCaseAddSingleton(exp);
			}
			
			//Todo translationState is mutable so it would not have to be threaded through?
			private Pair<TranslationState, Constraint> buildConstraint(TranslationState translationState, Operator op, List<RTLExpression> elist) {
				int elistSize = elist.size();
				Constraint constraint;
				List<Integer> idList;
				int id1;
				int id2;
				RTLExpression ex1;
				RTLExpression ex2;
				RTLOperation op1;
				RTLOperation op2;
				Pair<TranslationState, Constraint> op1Res;
				Pair<TranslationState, Constraint> op2Res;
				switch(op) {
				case EQUAL:
				case LESS:
				case LESS_OR_EQUAL:
				case UNSIGNED_LESS:
				case UNSIGNED_LESS_OR_EQUAL:
					assert elistSize == 2 : "Malformed comparison";
					ex1 = elist.get(0);
					assert rtlExpOkForRelOp(ex1) : "First operand (" + ex1 + ") not ok for " + op;
					ex2 = elist.get(1);
					assert rtlExpOkForRelOp(ex2) : "Second operand (" + ex2 + ") not ok for " + op;
					idList = translationState.addOperandGroup(elist);
					id1 = idList.get(0);
					id2 = idList.get(1);
					switch(op) {
					case EQUAL:
						constraint = Constraint$.MODULE$.createEq(id1, id2);
						break;
					case LESS:
						constraint = Constraint$.MODULE$.createLt(id1, id2);
						break;
					case LESS_OR_EQUAL:
						constraint = Constraint$.MODULE$.createLte(id1,  id2);
						break;
					case UNSIGNED_LESS:
						constraint = Constraint$.MODULE$.createULt(id1, id2);
						break;
					default:
						constraint = Constraint$.MODULE$.createULte(id1, id2);
						break;
					}
					return new Pair<TranslationState, Constraint>(translationState, constraint);
				case AND:
				case OR:
					assert elistSize >= 2 : "Malformed connective";
					if(elistSize == 2) {
						ex1 = convertBoolean(elist.get(0));
						ex2 = convertBoolean(elist.get(1));
						assert ex1 instanceof RTLOperation : ex1 + " is " + ex1.getClass() + ". required: RTLOperation";
						assert ex2 instanceof RTLOperation : ex2 + " is " + ex2.getClass() + ". required: RTLOperation";
						op1 = (RTLOperation) ex1;
						op2 = (RTLOperation) ex2;
						op1Res = buildConstraint(translationState, op1.getOperator(), Arrays.asList(op1.getOperands()));
						op2Res = buildConstraint(op1Res.getLeft(), op2.getOperator(), Arrays.asList(op2.getOperands()));
						switch(op) {
						case AND:
							constraint = Constraint$.MODULE$.createAnd(op1Res.getRight(), op2Res.getRight());
							break;
						default:
							constraint = Constraint$.MODULE$.createOr(op1Res.getRight(), op2Res.getRight());
							break;
						}
						return new Pair<TranslationState, Constraint>(op2Res.getLeft(), constraint);
					} else {
						ex1 = convertBoolean(elist.get(0));
						assert ex1 instanceof RTLOperation : ex1 + " is " + ex1.getClass() + ". required: RTLOperation";
						op1 = (RTLOperation) ex1;
						op1Res = buildConstraint(translationState, op1.getOperator(), Arrays.asList(op1.getOperands()));
						op2Res = buildConstraint(op1Res.getLeft(), op, elist.subList(1, elistSize));
						constraint = Constraint$.MODULE$.createAnd(op1Res.getRight(), op2Res.getRight());
						return new Pair<TranslationState, Constraint>(op2Res.getLeft(), constraint);
					}
				case NOT:
					assert elistSize == 1 : "Malformed not";
					ex1 = convertBoolean(elist.get(0));
					assert ex1 instanceof RTLOperation : ex1 + " is " + ex1.getClass() + ". required: RTLOperation";
					op1 = (RTLOperation) ex1;
					op1Res = buildConstraint(translationState, op1.getOperator(), Arrays.asList(op1.getOperands()));
					constraint = Constraint$.MODULE$.createNot(op1Res.getRight());
					return new Pair<TranslationState, Constraint>(op1Res.getLeft(), constraint);
				case XOR:
					//TODO lift restriction to two operands
					assert elistSize == 2 : "Malformed xor";
					ex1 = convertBoolean(elist.get(0));
					ex2 = convertBoolean(elist.get(1));
					assert ex1 instanceof RTLOperation : ex1 + " is " + ex1.getClass() + ". required: RTLOperation";
					assert ex2 instanceof RTLOperation : ex2 + " is " + ex2.getClass() + ". required: RTLOperation";
					op1 = (RTLOperation) ex1;
					op2 = (RTLOperation) ex2;
					op1Res = buildConstraint(translationState, op1.getOperator(), Arrays.asList(op1.getOperands()));
					op2Res = buildConstraint(op1Res.getLeft(), op2.getOperator(), Arrays.asList(op2.getOperands()));
					//not a and b or a and not b
					constraint = Constraint$.MODULE$.createOr(
							Constraint$.MODULE$.createAnd(Constraint$.MODULE$.createNot(op1Res.getRight()), op2Res.getRight())
							,
							Constraint$.MODULE$.createAnd(op1Res.getRight(), Constraint$.MODULE$.createNot(op2Res.getRight())));
					return new Pair<TranslationState, Constraint>(op2Res.getLeft(), constraint);
				default:
					assert false : "Unhandled assume: " + op;
					return null;
				}
			}
			
			/*private RTLOperation switchBinaryExp(RTLOperation oper) {
				assert oper.getOperandCount() == 2 : "switchBinaryExp(" + oper + "): Wrong arity: " + oper.getOperandCount() + " but con only handle 2";
				RTLExpression[] reversed = new RTLExpression[oper.getOperandCount()];
				for(int i = 0; i < oper.getOperandCount(); i++)
					reversed[i] = oper.getOperands()[oper.getOperandCount() - i - 1];
				return (RTLOperation) ExpressionFactory.createOperation(oper.getOperator(), reversed);
			}*/

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				logger.verbose("Found RTLAssume: " + stmt);
				BDDSet truthValue = abstractEval(stmt.getAssumption());

				//if truthValue = False -> infeasible
				// else if True -> fine...
				// else work to do!
				if(truthValue.isSingleton()) {
					if(truthValue.lessOrEqual(BDDSet.TRUE)) {
						logger.debug("truthValue TRUE for " + stmt + " (" + truthValue + ")");
						return thisState();
					} else {
						logger.info(stmt.getLabel() + ", state ID " + getIdentifier() + ": Transformer " + stmt + " is infeasible. ("+truthValue+")");
						return Collections.emptySet();
					}
				} else {
					//truth value either true or false -> reduction!
					RTLExpression assumption = stmt.getAssumption();
					assumption = assumption.evaluate(getContext());

					if(assumption instanceof RTLOperation) {
						RTLOperation operation = (RTLOperation) assumption;
						Pair<TranslationState, Constraint> converted;
						Map<Integer, IntLikeSet<Long, RTLNumber>> valid;
						BDDState post = copyThisState();
						try{
							converted = buildConstraint(new TranslationState(), operation.getOperator(), Arrays.asList(operation.getOperands()));
							logger.debug("==> Built constraint: " + converted + " for RTLAssume: " + assumption + " and State: " + BDDState.this);
							valid = converted.getRight().solveJLong(converted.getLeft().getValueMap(), rtlNumberIsDynBounded, rtlNumberIsDynBoundedBits, rtlNumberIsOrdered, rtlNumberToLongBWCaster, longBWToRTLNumberCaster);
							logger.debug("==>> Valid: " + valid);
						} catch (Exception e) {
							logger.debug("failed to build constraint for: " + assumption + " with: " + e);
							if(Options.failFast.getValue()) throw e;
							return thisState();
						} catch (AssertionError e) {
							logger.debug("failed to build constraint for: " + assumption + " with: " + e);
							if(Options.failFast.getValue() && Options.debug.getValue()) throw e;
							return thisState();
						}
						TranslationState tState = converted.getLeft();

						for(Map.Entry<Integer, RTLExpression> entry : tState.getBackMap().entrySet()) {
							logger.debug("processing entry: " + entry);
							int id = entry.getKey();
							IntLikeSet<Long, RTLNumber> intlikeset = valid.get(id);
							MemoryRegion region = tState.getRegionMap().get(id);
							RTLExpression exp = entry.getValue();
							if(region.isTop()){
								logger.debug("Region top from Constraint System. Skipping: " + id + " = " + exp);
								continue;
							}
							BDDSet value = new BDDSet(intlikeset, region);
							assert exp != null : "exp == null";
							assert value != null : "value == null";
							assert region != null : "region == null";
							if(exp instanceof RTLVariable) {
								RTLVariable var = (RTLVariable) exp;
								BDDSet oldValue = getValue(var);
								BDDSet newValue = oldValue.meet(value);
								if(newValue.getSet().isEmpty()) return Collections.emptySet();
								scala.collection.immutable.List<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> eqs = equivalences.lookup(variable(var));
								if(!eqs.isEmpty()) logger.debug("equivalence: found equivalences " + eqs + " for assumption " + assumption + " (" + stmt.getLabel() + ")");
								for(scala.collection.Iterator<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> it = eqs.iterator(); it.hasNext();) {
									StorageEntity<MemoryRegion, RTLNumber, RTLVariable> entity = it.next();
									if(entity instanceof MemLoc) {
										MemLoc<MemoryRegion, RTLNumber, RTLVariable> memloc = (MemLoc<MemoryRegion, RTLNumber, RTLVariable>) entity;
										BDDSet addr = BDDSet.singleton(memloc.region(), memloc.address());
										logger.debug("equivalence: applying equivalence " + variable(var) + " = " + entity + " (" + stmt.getLabel() + "); old: " + post.getMemoryValue(addr, memloc.address().getBitWidth()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
										post.setMemoryValue(addr, memloc.address().getBitWidth(), newValue);
									} else if(entity instanceof Variable) {
										Variable<MemoryRegion, RTLNumber, RTLVariable> variable = (Variable<MemoryRegion, RTLNumber, RTLVariable>) entity;
										logger.debug("equivalence: applying equivalence " + variable(var) + " = " + entity + " (" + stmt.getLabel() + "); old: " + getValue(variable.variable()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
										post.setValue(variable.variable(), newValue);
									}
								}
								post.setValue(var, newValue);
							} else if(exp instanceof RTLMemoryLocation) {
								RTLMemoryLocation memLoc = (RTLMemoryLocation) exp;
								BDDSet evaledAddress = post.abstractEvalAddress(memLoc);
								BDDSet oldValue = post.getMemoryValue(evaledAddress, memLoc.getBitWidth());
								BDDSet newValue = oldValue.meet(value);
								if(newValue.getSet().isEmpty()) return Collections.emptySet();
								if(evaledAddress.isSingleton()) {
									scala.collection.immutable.List<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> eqs = equivalences.lookup(memLoc(evaledAddress.getRegion(), evaledAddress.randomElement()));
									if (!eqs.isEmpty())
										logger.debug("equivalence: found equivalences " + eqs + " for assumption " + assumption + " (" + stmt.getLabel() + ")");
									for(scala.collection.Iterator<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> it = eqs.iterator(); it.hasNext();) {
										StorageEntity<MemoryRegion, RTLNumber, RTLVariable> entity = it.next();
										if(entity instanceof MemLoc) {
											MemLoc<MemoryRegion, RTLNumber, RTLVariable> memloc = (MemLoc<MemoryRegion, RTLNumber, RTLVariable>) entity;
											BDDSet addr = BDDSet.singleton(memloc.region(), memloc.address());
											logger.debug("equivalence: applying equivalence " + memLoc(evaledAddress.getRegion(), evaledAddress.randomElement()) + " = " + entity + " (" + stmt.getLabel() + "); old: " + post.getMemoryValue(addr, memloc.address().getBitWidth()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
											post.setMemoryValue(addr, memloc.address().getBitWidth(), newValue);
										} else if(entity instanceof Variable) {
											Variable<MemoryRegion, RTLNumber, RTLVariable> variable = (Variable<MemoryRegion, RTLNumber, RTLVariable>) entity;
											logger.debug("equivalence: applying equivalence " + memLoc(evaledAddress.getRegion(), evaledAddress.randomElement()) + " = " + entity + " (" + stmt.getLabel() + "); old: " + getValue(variable.variable()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
											post.setValue(variable.variable(), newValue);
										}
									}
								}
								post.setMemoryValue(evaledAddress, memLoc.getBitWidth(), newValue);
							} else if(exp instanceof RTLOperation) {
								RTLOperation op = (RTLOperation) exp;
								if(specialCaseBAndSingleton(op)) {
									//XXX may be possible to lift this restriction
									if(value.isSingleton() 
											|| (new BDDSet(value.getSet().invert(), value.getRegion())).isSingleton()) {
										RTLNumber n = null;
										RTLVariable v = null;
										RTLExpression[] exps = op.getOperands();
										if(exps[0] instanceof RTLNumber && exps[1] instanceof RTLVariable) {
											n = (RTLNumber) exps[0];
											v = (RTLVariable) exps[1];
										} else {
											n = (RTLNumber) exps[1];
											v = (RTLVariable) exps[0];
										}
										scala.collection.immutable.List<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> eqs = equivalences.lookup(variable(v));
										logger.debug("n: "+n+" v: "+v);
										assert n != null && v != null : "Special case restriction failure";
										BDDSet oldValue = getValue(v);
										BDDSet nSingleton = BDDSet.singleton(n);
										assert nSingleton.getBitWidth() == value.getBitWidth() : "Constraint System: FAIL - bits (" + nSingleton.getBitWidth() + ", " + value.getBitWidth() + ")";
										//assert nSingleton.getRegion() == value.getRegion() : "Constraint System: FAIL - regions (" + nSingleton.getRegion() + ", " + value.getRegion() + ")";
										if(value.isSingleton()) {
											if(nSingleton.getSet().bNot().bAnd(value.getSet()).randomElement().longValue() == 0L) {
												logger.debug("Value: " + value + ", nSingleton: " + nSingleton);
												BDDSet newValue = new BDDSet(oldValue.getSet().bAnd(nSingleton.getSet().bNot()).bOr(value.getSet()), region);
												logger.debug("1: oldValue: " + oldValue + ", newValue: " + newValue);
												if (!eqs.isEmpty())
													logger.debug("equivalence: found equivalences " + eqs + " for assumption " + assumption + " (" + stmt.getLabel() + ")");
												for(scala.collection.Iterator<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> it = eqs.iterator(); it.hasNext();) {
													StorageEntity<MemoryRegion, RTLNumber, RTLVariable> entity = it.next();
													if(entity instanceof MemLoc) {
														MemLoc<MemoryRegion, RTLNumber, RTLVariable> memloc = (MemLoc<MemoryRegion, RTLNumber, RTLVariable>) entity;
														BDDSet addr = BDDSet.singleton(memloc.region(), memloc.address());
														logger.debug("equivalence: applying equivalence " + variable(v) + " = " + entity + " (" + stmt.getLabel() + "); old: " + post.getMemoryValue(addr, memloc.address().getBitWidth()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
														post.setMemoryValue(addr, memloc.address().getBitWidth(), newValue);
													} else if(entity instanceof Variable) {
														Variable<MemoryRegion, RTLNumber, RTLVariable> variable = (Variable<MemoryRegion, RTLNumber, RTLVariable>) entity;
														logger.debug("equivalence: applying equivalence " + variable(v) + " = " + entity + " (" + stmt.getLabel() + "); old: " + getValue(variable.variable()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
														post.setValue(variable.variable(), newValue);
													}
												}
												post.setValue(v, newValue);
											} else return Collections.emptySet();
										} else {
											if(nSingleton.getSet().bNot().bAnd(value.getSet().invert()).randomElement().longValue() == 0L) {
												BDDSet notAllowed = new BDDSet(oldValue.getSet().bAnd(nSingleton.getSet().bNot()).bOr(value.getSet().invert()), oldValue.getRegion());
												logger.debug("notAllowed: " + notAllowed);
												BDDSet newValue = new BDDSet(oldValue.getSet().intersect(notAllowed.getSet().invert()), region);
												logger.debug("2: oldValue: " + oldValue + ", newValue: " + newValue);
												if (!eqs.isEmpty())
													logger.debug("equivalence: found equivalences " + eqs + " for assumption " + assumption + " (" + stmt.getLabel() + ")");
												for(scala.collection.Iterator<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> it = eqs.iterator(); it.hasNext();) {
													StorageEntity<MemoryRegion, RTLNumber, RTLVariable> entity = it.next();
													if(entity instanceof MemLoc) {
														MemLoc<MemoryRegion, RTLNumber, RTLVariable> memloc = (MemLoc<MemoryRegion, RTLNumber, RTLVariable>) entity;
														BDDSet addr = BDDSet.singleton(memloc.region(), memloc.address());
														logger.debug("equivalence: applying equivalence " + variable(v) + " = " + entity + " (" + stmt.getLabel() + "); old: " + post.getMemoryValue(addr, memloc.address().getBitWidth()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
														post.setMemoryValue(addr, memloc.address().getBitWidth(), newValue);
													} else if(entity instanceof Variable) {
														Variable<MemoryRegion, RTLNumber, RTLVariable> variable = (Variable<MemoryRegion, RTLNumber, RTLVariable>) entity;
														logger.debug("equivalence: applying equivalence " + variable(v) + " = " + entity + " (" + stmt.getLabel() + "); old: " + getValue(variable.variable()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
														post.setValue(variable.variable(), newValue);
													}
												}
												post.setValue(v, newValue);
											} else return Collections.emptySet();
										}
									} else logger.error("Constraint System: Skipping restriction for specialCaseBAndSingleton (" + exp + ")");
								} else if(specialCaseAddSingleton(op)) {
									RTLNumber constant;
									RTLVariable var;
									if(op.getOperands()[0] instanceof RTLNumber) {
										constant = (RTLNumber) op.getOperands()[0];
										var = (RTLVariable) op.getOperands()[1];
									} else {
										constant = (RTLNumber) op.getOperands()[1];
										var = (RTLVariable) op.getOperands()[0];
									}
									scala.collection.immutable.List<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> eqs = equivalences.lookup(variable(var));
									BDDSet newValue = value.plus(BDDSet.singleton(constant).negate());
									if(newValue.getSet().isEmpty()) return Collections.emptySet();
									if (!eqs.isEmpty())
										logger.debug("equivalence: found equivalences " + eqs + " for assumption " + assumption + " (" + stmt.getLabel() + ")");
									for(scala.collection.Iterator<StorageEntity<MemoryRegion, RTLNumber, RTLVariable>> it = eqs.iterator(); it.hasNext();) {
										StorageEntity<MemoryRegion, RTLNumber, RTLVariable> entity = it.next();
										if(entity instanceof MemLoc) {
											MemLoc<MemoryRegion, RTLNumber, RTLVariable> memloc = (MemLoc<MemoryRegion, RTLNumber, RTLVariable>) entity;
											BDDSet addr = BDDSet.singleton(memloc.region(), memloc.address());
											logger.debug("equivalence: applying equivalence " + variable(var) + " = " + entity + " (" + stmt.getLabel() + "); old: " + post.getMemoryValue(addr, memloc.address().getBitWidth()).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
											post.setMemoryValue(addr, memloc.address().getBitWidth(), newValue);
										} else if(entity instanceof Variable) {
											Variable<MemoryRegion, RTLNumber, RTLVariable> variable = (Variable<MemoryRegion, RTLNumber, RTLVariable>) entity;
											logger.debug("equivalence: applying equivalence " + variable(var) + " = " + entity + " (" + stmt.getLabel() + "); old: " + getValue(var).getSet().sizeBigInt() + " new: " + newValue.getSet().sizeBigInt());
											post.setValue(variable.variable(), newValue);
										}
									}
									post.setValue(var, newValue);
								}else logger.error("Constraint System: Unhandled special case (" + exp + ") during restriction");
							} else logger.error("Constraint System: Unhandled type (" + exp.getClass() + ") during restriction");
						}
						logger.verbose("new state from Constraint System:" + post);
						return Collections.singleton((AbstractState) post);
						
//						//XXX
//						switch(operation.getOperator()) {
//						case EQUAL:
//							logger.debug("Handling RTLAssume: " + stmt);
//							if(operation.getOperands()[1] instanceof RTLVariable
//							&& operation.getOperands()[0] instanceof RTLNumber) {
//								return visit(new RTLAssume(switchBinaryExp(operation), stmt.getSource()));
//							} else if(operation.getOperands()[0] instanceof RTLVariable
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLVariable var = (RTLVariable) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								post.setValue(var, BDDSet.singleton(num));
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[1] instanceof RTLMemoryLocation
//								   && operation.getOperands()[0] instanceof RTLNumber) {
//								return visit(new RTLAssume(switchBinaryExp(operation), stmt.getSource()));
//							} else if(operation.getOperands()[0] instanceof RTLMemoryLocation
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLMemoryLocation mem = (RTLMemoryLocation) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								BDDSet evaledAddress = post.abstractEval(mem.getAddress());
//								post.setMemoryValue(evaledAddress, mem.getBitWidth(), BDDSet.singleton(num));
//								return Collections.singleton((AbstractState) post);
//							}
//						case LESS_OR_EQUAL:
//							logger.debug("Handling RTLAssume: " + stmt);
//							if(operation.getOperands()[1] instanceof RTLVariable
//							&& operation.getOperands()[0] instanceof RTLNumber) {
//								RTLVariable var = (RTLVariable) operation.getOperands()[1];
//								RTLNumber num = (RTLNumber) operation.getOperands()[0];
//								BDDState post = copyThisState();
//								BDDSet curr = post.getValue(var);
//								BDDSet restricted = new BDDSet(curr.getSet().restrictGreaterOrEqual(BDDSet.singleton(num).getSet()));
//								post.setValue(var, restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[0] instanceof RTLVariable
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLVariable var = (RTLVariable) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								BDDSet curr = post.getValue(var);
//								BDDSet restricted = new BDDSet(curr.getSet().restrictLessOrEqual(BDDSet.singleton(num).getSet()));
//								post.setValue(var, restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[1] instanceof RTLMemoryLocation
//								   && operation.getOperands()[0] instanceof RTLNumber) {
//								RTLMemoryLocation mem = (RTLMemoryLocation) operation.getOperands()[1];
//								RTLNumber num = (RTLNumber) operation.getOperands()[0];
//								BDDState post = copyThisState();
//								BDDSet evaledAddress = post.abstractEval(mem.getAddress());
//								BDDSet curr = post.getMemoryValue(evaledAddress, mem.getBitWidth());
//								BDDSet restricted = new BDDSet(curr.getSet().restrictGreaterOrEqual(BDDSet.singleton(num).getSet()));
//								post.setMemoryValue(evaledAddress, mem.getBitWidth(), restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[0] instanceof RTLMemoryLocation
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLMemoryLocation mem = (RTLMemoryLocation) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								BDDSet evaledAddress = post.abstractEval(mem.getAddress());
//								BDDSet curr = post.getMemoryValue(evaledAddress, mem.getBitWidth());
//								BDDSet restricted = new BDDSet(curr.getSet().restrictLessOrEqual(BDDSet.singleton(num).getSet()));
//								post.setMemoryValue(evaledAddress, mem.getBitWidth(), restricted);
//								return Collections.singleton((AbstractState) post);
//							}
//						case LESS:
//							logger.debug("Handling RTLAssume: " + stmt);
//							if(operation.getOperands()[1] instanceof RTLVariable
//							&& operation.getOperands()[0] instanceof RTLNumber) {
//								RTLVariable var = (RTLVariable) operation.getOperands()[1];
//								RTLNumber num = (RTLNumber) operation.getOperands()[0];
//								BDDState post = copyThisState();
//								BDDSet curr = post.getValue(var);
//								BDDSet restricted = new BDDSet(curr.getSet().restrictGreater(BDDSet.singleton(num).getSet()));
//								post.setValue(var, restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[0] instanceof RTLVariable
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLVariable var = (RTLVariable) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								BDDSet curr = post.getValue(var);
//								BDDSet restricted = new BDDSet(curr.getSet().restrictLess(BDDSet.singleton(num).getSet()));
//								post.setValue(var, restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[1] instanceof RTLMemoryLocation
//								   && operation.getOperands()[0] instanceof RTLNumber) {
//								RTLMemoryLocation mem = (RTLMemoryLocation) operation.getOperands()[1];
//								RTLNumber num = (RTLNumber) operation.getOperands()[0];
//								BDDState post = copyThisState();
//								BDDSet evaledAddress = post.abstractEval(mem.getAddress());
//								BDDSet curr = post.getMemoryValue(evaledAddress, mem.getBitWidth());
//								BDDSet restricted = new BDDSet(curr.getSet().restrictGreater(BDDSet.singleton(num).getSet()));
//								post.setMemoryValue(evaledAddress, mem.getBitWidth(), restricted);
//								return Collections.singleton((AbstractState) post);
//							} else if(operation.getOperands()[0] instanceof RTLMemoryLocation
//								   && operation.getOperands()[1] instanceof RTLNumber) {
//								RTLMemoryLocation mem = (RTLMemoryLocation) operation.getOperands()[0];
//								RTLNumber num = (RTLNumber) operation.getOperands()[1];
//								BDDState post = copyThisState();
//								BDDSet evaledAddress = post.abstractEval(mem.getAddress());
//								BDDSet curr = post.getMemoryValue(evaledAddress, mem.getBitWidth());
//								BDDSet restricted = new BDDSet(curr.getSet().restrictLess(BDDSet.singleton(num).getSet()));
//								post.setMemoryValue(evaledAddress, mem.getBitWidth(), restricted);
//								return Collections.singleton((AbstractState) post);
//							}
//						default:
//							logger.debug("XXX RTLAssume(" + operation + ") - we ignored that. An opportunity missed...");
//							break;
//						}
					}
				}
				logger.warn("Ignoring RTLAssume: " + stmt);
				return Collections.singleton((AbstractState) copyThisState());
			}

			/*XXX SCM: Complete copy - no idea if correct...
			 * Allocation counter is tree that counts nodes to top if location of node == current...
			 * Ok, why the hell not
			 */
			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				BDDState post = copyThisState();
				Writable lhs = stmt.getPointer();
				// Note: We never need to create heap regions as summary regions. Either the threshold
				// is high enough to precisely track all executions of an allocation explicitly,
				// or the number of different pointers/regions also exceeds the threshold and
				// will be widened to T.
				// TODO: How can we create regions to allow exchange of information between analyses?
				//MemoryRegion newRegion = MemoryRegion.create("alloc" + stmt.getLabel() + "_" + getIdentifier());

				MemoryRegion newRegion;

				// Check for hardcoded allocation names (i.e., stack or FS)
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					newRegion = MemoryRegion.create("alloc" + stmt.getLabel() + 
							"#" + post.allocationCounter.countAllocation(stmt.getLabel()));
				}

				// We also allow pointers of less than the actual address size, to emulate the 16 bit segment registers FS/GS
				// FS gets a value of (FS, 0) in the prologue. 

				if (lhs instanceof RTLVariable) {
					post.setValue((RTLVariable)lhs, BDDSet.singleton(newRegion, 
							ExpressionFactory.createNumber(0, lhs.getBitWidth())));
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					BDDSet abstractAddress = abstractEvalAddress(m);
					if (!post.setMemoryValue(abstractAddress, m.getBitWidth(), 
							BDDSet.singleton(newRegion, 
									ExpressionFactory.createNumber(0, lhs.getBitWidth()))))
						logger.verbose(stmt.getLabel() + ": Cannot resolve memory write from alloc to " + m + ".");
				}

				return Collections.singleton((AbstractState)post);
			}

			//Complete copy again.
			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				BDDState post = copyThisState();
				BDDSet abstractAddress = abstractEval(stmt.getPointer());
				// if the address cannot be determined, set all store memory to TOP
				if (abstractAddress.isTop()) {
					logger.info(getIdentifier() + ": Cannot resolve location of deallocated memory pointer " + stmt.getPointer() + ". Might miss use after free bugs!");
					//logger.info(getIdentifier() + ": Cannot resolve location of deallocated memory pointer " + stmt.getPointer() + ". Defaulting ALL memory to " + Characters.TOP);
					//logger.info(BasedNumberValuation.this);
					//post.aStore.setTop();
				} else {
					if (abstractAddress.getRegion() == MemoryRegion.GLOBAL || abstractAddress.getRegion() == MemoryRegion.STACK) 
						throw new UnknownPointerAccessException("Cannot deallocate " + abstractAddress.getRegion() + "!");
					logger.debug(stmt.getLabel() + ": Dealloc on " + abstractAddress.getRegion()); 
					post.abstractMemoryTable.setTop(abstractAddress.getRegion());
				}
				return Collections.singleton((AbstractState)post);
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				BDDState post = copyThisState();
				for(RTLVariable var : stmt.getDefinedVariables())
					post.setValue(var, BDDSet.topBW(var.getBitWidth()));
				post.abstractMemoryTable.setTop();
				return Collections.singleton((AbstractState) post);
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				//TODO SCM implement, maybe?
				return Collections.singleton((AbstractState) copyThisState());
			}

			/*XXX scm : Do not understand BitWidths here, really
			 * what if "cell" is not big enough?
			 * Otherwise should be fine - memset sets same value everywhere
			 * Check!
			 * 
			 * Do I need unique count? could also deal with abstractCount.getSet().max() ?
			 */
			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				BDDState post = copyThisState();

				BDDSet abstractDestination = abstractEval(stmt.getDestination());
				BDDSet abstractValue = abstractEval(stmt.getValue());
				BDDSet abstractCount = abstractEval(stmt.getCount());

				logger.debug(stmt.getLabel() + ": memset(" + abstractDestination + ", " + abstractValue + ", " + abstractCount + ")");

				if(abstractCount.hasUniqueConcretization()
						&& !abstractDestination.isTop()
						&& !abstractDestination.getSet().isFull()) {
					if(!abstractDestination.isSingleton())
						logger.debug(stmt.getLabel() + ": More than one destination memset(" + abstractDestination + ", " + abstractValue + ", " + abstractCount + ")");
					int step = abstractValue.getBitWidth() / 8;
					long count = abstractCount.getSet().randomElement().longValue();
					for(RTLNumber rtlnum : abstractDestination.concretize()) {
						long base = rtlnum.longValue();
						for(long i = base; i < base + (count * step); i += step) {
							BDDSet pointer = BDDSet.singleton(abstractDestination.getRegion(), ExpressionFactory.createNumber(i, abstractDestination.getBitWidth()));
							post.setMemoryValue(pointer, abstractValue.getBitWidth(), abstractValue);
						}
					}
				} else {
					logger.info(stmt.getLabel() + ": Overapproximating memset(" + abstractDestination + ", " + abstractValue + ", " + abstractCount + ")");
					post.abstractMemoryTable.setTop(abstractDestination.getRegion());
				}
				return Collections.singleton((AbstractState) post);
			}

			//XXX scm: see function for RTLMemset
			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				BDDState post = copyThisState();

				BDDSet abstractSource = abstractEval(stmt.getSource());
				BDDSet abstractDestination = abstractEval(stmt.getDestination());
				BDDSet abstractSize = abstractEval(stmt.getSize());

				logger.debug(stmt.getLabel() + ": memcpy(" + abstractSource + ", " + abstractDestination + ", " + abstractSize + ")");

				/*force everything to be unique for now - will probably not work but have to be less carefull.
				 * othwerwise i would have to join all possible values in destination - yak!
				 */
				if(abstractSize.hasUniqueConcretization()
						&& !abstractDestination.isTop()
						&& abstractDestination.isSingleton()
						&& !abstractSource.isTop()
						&& abstractSource.isSingleton()) {
					post.abstractMemoryTable.memcpy(abstractSource.getRegion()
							,abstractSource.getSet().randomElement().longValue()
							,abstractDestination.getRegion()
							,abstractDestination.getSet().randomElement().longValue()
							,abstractSize.getSet().randomElement().longValue());
				} else {
					logger.info(stmt.getLabel() + ": Overapproximating memcpy(" + abstractDestination + ", " + abstractDestination + ", " + abstractSize + ")");
					post.abstractMemoryTable.setTop(abstractDestination.getRegion());
				}
				return Collections.singleton((AbstractState) post);
			}

			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				return thisState();
			}

		});
		
		logger.debug("finished abstractPost(" + statement + ") in state: " + this.toString() + " with result: " + res);
		return res;
	}



}
