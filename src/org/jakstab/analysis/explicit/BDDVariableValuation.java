package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Map;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.VariableValuation;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLBitRange;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;

import cc.sven.tlike.IntLikeSet;

public class BDDVariableValuation extends VariableValuation<BDDSet> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BDDVariableValuation.class);

	public BDDVariableValuation(AbstractValueFactory<BDDSet> valueFactory) {
		super(valueFactory);
	}

	public BDDVariableValuation(BDDSetFactory bddSetFactory) {
		super(bddSetFactory);
	}

	public BDDVariableValuation(BDDVariableValuation abstractVarTable) {
		super(abstractVarTable);
	}

	@SuppressWarnings("unchecked")
	@Override
	public BDDVariableValuation join(LatticeElement l) {
		BDDVariableValuation other = (BDDVariableValuation)l;
			if (isTop() || other.isBot()) return this;
			if (isBot() || other.isTop()) return other;

			BDDVariableValuation joinedValuation = new BDDVariableValuation(valueFactory);
			// Join variable valuations
			for (Map.Entry<RTLVariable,BDDSet> entry : aVarVal.entrySet()) {
				RTLVariable var = entry.getKey();
				BDDSet value = entry.getValue();
				joinedValuation.set(var, (BDDSet)value.join(other.get(var)));
			}
					
			return joinedValuation;

	}

	@Override
	public BDDSet get(RTLVariable var) {
		logger.debug("getting var: " + var );
		BDDSet e = aVarVal.get(var);
		if (e != null) {
			return e;
		} else {
			// See if we can get the value from a covering register
			RTLBitRange asParent = ExpressionFactory.getRegisterAsParent(var);

			if (asParent != null && asParent.getOperand() instanceof RTLVariable) {
				RTLVariable parent = (RTLVariable)asParent.getOperand();
				// Recursive call for al -> ax -> eax 
				BDDSet parentVal = get(parent);
				assert parentVal != null;
				
				if(parentVal.isTop()) 
					return valueFactory.createTop(var.getBitWidth());

				logger.debug("asParent: " + asParent + " parent: " + parent + " parentVal: " + parentVal);

				int first = ((RTLNumber)asParent.getFirstBitIndex()).intValue();
				int last = ((RTLNumber)asParent.getLastBitIndex()).intValue();
				IntLikeSet<Long, RTLNumber> ret = parentVal.getSet().bitExtract(last,first); // TODO observe
				logger.debug("first: "+first +" last: "+last+" extractedValue: " + ret);
				return new BDDSet(ret,parentVal.getRegion());
			}

			return valueFactory.createTop(var.getBitWidth());
		}
	}
	
	@SuppressWarnings("unchecked")
	@Override
	public void set(RTLVariable var, BDDSet value) {
		logger.debug("setting var: " + var + " to value: " + value);
		RTLBitRange asParent = ExpressionFactory.getRegisterAsParent(var);

		// Set parent register - we only do this if the value to set represents 
		// a single concrete value. If we want to generalize this, we have to
		// build the cartesian product of concretizations
		if (asParent != null && asParent.getOperand() instanceof RTLVariable) {
			
			RTLVariable parent = (RTLVariable)asParent.getOperand();
			BDDSet parentVal = get(parent);
			
			logger.debug("asParent: " + asParent + " parent: " + parent + " parentVal: " + parentVal);
			
			int firstBit = ((RTLNumber)asParent.getFirstBitIndex()).intValue();
			int lastBit = ((RTLNumber)asParent.getLastBitIndex()).intValue();
			long bitMask = RTLBitRange.bitMask(0, firstBit - 1) | 
					RTLBitRange.bitMask(lastBit + 1, asParent.getOperand().getBitWidth());

			IntLikeSet<Long, RTLNumber> maskedParent = parentVal.getSet().bAnd(valueFactory.createAbstractValue(ExpressionFactory.createNumber(bitMask,parentVal.getBitWidth())).getSet());
			IntLikeSet<Long, RTLNumber> shiftedValue = value.getSet().zeroFill(parentVal.getBitWidth()-1, value.getBitWidth()-1).bShl(firstBit);

			MemoryRegion region = value.getRegion().join(parentVal.getRegion());
			if(region.isTop()) {
				set(parent, new BDDSet(maskedParent.bOr(shiftedValue),value.getRegion()));
			} else {
				set(parent, new BDDSet(maskedParent.bOr(shiftedValue),region));
			}
			return;
		}

		clearCovering(var);
		clearCovered(var);
		
		if (value.isTop()) {
			aVarVal.remove(var);
		} else {
			logger.debug("putting var: " + var + " to value: " + value);
			aVarVal.put(var, value);
		}
	}
}
