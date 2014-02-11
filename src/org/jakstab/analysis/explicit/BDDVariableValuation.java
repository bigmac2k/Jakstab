package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.LinkedList;
import java.util.Map;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.VariableValuation;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLBitRange;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;

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
				

				logger.debug(parent);
				logger.debug(asParent);
				logger.debug(parentVal);
				
				int first = ((RTLNumber)asParent.getFirstBitIndex()).intValue();
				int last = ((RTLNumber)asParent.getLastBitIndex()).intValue();
				return new BDDSet(parentVal.getSet().bitExtract(last,first),parentVal.getRegion());
			}

			return valueFactory.createTop(var.getBitWidth());
		}
	}
}
