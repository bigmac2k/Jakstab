/*
 * KSetAnalysis.java - This file is part of the Jakstab project.
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
package org.jakstab.analysis.explicit;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.analysis.intervals.IntervalElement;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

/**
 * A K-Set analysis as used for the example in the VMCAI'09 paper. It 
 * represents values as sets of a constant size, merging them to TOP if
 * the bound is exceeded. Supports memory values and register aliasing
 * through the generic VariableValuation class.
 * 
 * For programs with procedure calls, it should be used together with a 
 * call-stack analysis for context sensitivity. Otherwise, it will merge
 * the stack contents from different calling contexts, which leads to
 * illegal addresses used as jump targets on return. 
 */
public class WSetAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('w');
		p.setName("W-Set analysis");
		p.setDescription("For each variable, collect values per location (non-relational).");
		p.setExplicit(true);
	}
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(WSetAnalysis.class);
	
	private AbstractValueFactory<WSet> valueFactory;

	public WSetAnalysis() {
		valueFactory = new WSetFactory();
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		return null;
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new ValuationState(valueFactory);
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		return CPAOperators.mergeJoin(s1, s2, precision);
	}

	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {

		final RTLStatement statement = (RTLStatement)cfaEdge.getTransformer();
		final ValuationState iState = (ValuationState)state;
		return Collections.singleton(statement.accept(new DefaultStatementVisitor<AbstractState>() {

			@Override
			public AbstractState visit(RTLAlloc stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getPointer();

				MemoryRegion newRegion;
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					// TODO: Detect whether this allocation is unique to allow strong updates
					newRegion = MemoryRegion.createAsSummary("alloc" + stmt.getLabel());
				}
				
				WSet basePointer = new WSet( new BasedNumberElement(newRegion, 
						ExpressionFactory.createNumber(0, 32)));
				
				if (lhs instanceof RTLVariable) {
					post.setVariableValue((RTLVariable)lhs, basePointer); 
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
					post.setMemoryValue(evaledAddress, m.getBitWidth(), basePointer);
				}

				return post;
			}

			@Override
			public AbstractState visit(RTLVariableAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				AbstractDomainElement evaledRhs = iState.abstractEval(stmt.getRightHandSide());
				post.setVariableValue(stmt.getLeftHandSide(), evaledRhs);
				logger.debug(iState.getIdentifier() + iState);
				logger.debug("Evaluating Assingment: "  + stmt + " to: " + evaledRhs + " ("+ iState.getIdentifier() +", "+post.getIdentifier()+")");
				return post;
			}
			
			@Override
			public AbstractState visit(RTLMemoryAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				AbstractDomainElement evaledRhs = iState.abstractEval(stmt.getRightHandSide());
				RTLMemoryLocation m = stmt.getLeftHandSide();
				AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
				post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
				return post;
			}

			@Override
			public AbstractState visit(RTLAssume stmt) {
				if (stmt.getAssumption() instanceof RTLOperation) {
					RTLOperation operation = (RTLOperation)stmt.getAssumption(); 
					if (operation.getOperator() == Operator.EQUAL) {					
						RTLExpression lhs = operation.getOperands()[0];
						RTLExpression rhs = operation.getOperands()[1];
						AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
						if (lhs instanceof RTLVariable) {
							ValuationState post = new ValuationState(iState);
							post.setVariableValue((RTLVariable)lhs, evaledRhs);
							return post;
						} else if (lhs instanceof RTLMemoryLocation) {
							ValuationState post = new ValuationState(iState);
							RTLMemoryLocation m = (RTLMemoryLocation)lhs;
							AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
							post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
							return post;
						}
					} else if (operation.getOperator() == Operator.UNSIGNED_LESS_OR_EQUAL) {
						RTLExpression alhs = operation.getOperands()[0];
						RTLExpression arhs = operation.getOperands()[1];
						logger.debug(alhs + " <= " + arhs);
						if(arhs instanceof RTLNumber)
						{
							RTLNumber num = (RTLNumber) arhs;
							if(num.longValue()>=0) {
								IntervalElement uLessInt = new IntervalElement(ExpressionFactory.createNumber(0, num.getBitWidth()),num);

								if (alhs instanceof RTLVariable) {
									ValuationState post = new ValuationState(iState);
									post.setVariableValue((RTLVariable)alhs,
											valueFactory.createAbstractValue( uLessInt.concretize())
											.meet(iState.getVariableValue((RTLVariable)alhs)));
									return post;
								} else if (alhs instanceof RTLMemoryLocation) {
									ValuationState post = new ValuationState(iState);
									RTLMemoryLocation m = (RTLMemoryLocation)alhs;
									AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
									post.setMemoryValue(evaledAddress, m.getBitWidth(), 
											valueFactory.createAbstractValue(uLessInt.concretize())
											.meet(iState.getMemoryValue(evaledAddress, m.getBitWidth())));
									return post;
								}
							}
						}
					}
				}
				return iState;
			}

			@Override
			protected AbstractState visitDefault(RTLStatement stmt) {
				return iState;
			}

		}));

	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopJoin(s, reached, precision);
	}

	
	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {

		ValuationState state = (ValuationState)s;
		ValuationState strengthenedState = null;

		for (AbstractState t : otherStates) {
			// TODO: Does not work correctly if BoundedAddressTracking returns more than
			// 		 one successor state.
			if (t instanceof BasedNumberValuation) {
				BasedNumberValuation exState = (BasedNumberValuation)t;
				for (Map.Entry<RTLVariable, BasedNumberElement> entry : 
					exState.getVariableValuation()) {
					RTLVariable var = entry.getKey();
					BasedNumberElement exVal = entry.getValue();
					if (exVal.isTop() || exVal.isNumberTop())
						continue;
					if (state.getVariableValue(var).isTop()) {
						if (strengthenedState == null) {
							strengthenedState = new ValuationState(state);
						}
						AbstractDomainElement aggr = strengthenedState.getVariableValue(var);
						AbstractDomainElement e = new WSet(exVal);
						logger.debug(aggr);
						logger.debug(e);
						if(aggr.isTop()) {
							aggr = e;
						}
						aggr = aggr.join(e);
						//aggr = e;
						logger.debug(aggr);
						strengthenedState.setVariableValue(var, aggr );
						logger.debug("Strengthened state " + state.getIdentifier() + 
								" by setting " + var + " to " + exVal+ " (" + strengthenedState.getIdentifier() + ")");
						logger.debug(state);
						logger.debug(strengthenedState);
					}
				}
			}
		}
		
		return strengthenedState == null ? state : strengthenedState;
		//return state;
	}

}
