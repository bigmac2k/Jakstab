package org.jakstab.analysis.intervalsets;

import java.util.Collections;
import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.Program;
import org.jakstab.analysis.AbstractDomainElement;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.analysis.ValuationState;
import org.jakstab.analysis.intervals.IntervalAnalysis;
import org.jakstab.analysis.intervals.IntervalElement;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLOperation;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.expressions.Writable;
import org.jakstab.rtl.statements.DefaultStatementVisitor;
import org.jakstab.rtl.statements.RTLAlloc;
import org.jakstab.rtl.statements.RTLAssume;
import org.jakstab.rtl.statements.RTLHavoc;
import org.jakstab.rtl.statements.RTLMemoryAssignment;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.rtl.statements.RTLUnknownProcedureCall;
import org.jakstab.rtl.statements.RTLVariableAssignment;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

public class IntervalSetAnalysis implements ConfigurableProgramAnalysis{

	public static void register(AnalysisProperties p) {
		p.setShortHand('y');
		p.setName("Interval set analysis");
		p.setDescription("Compute sets of strided intervals with region information.");
		p.setExplicit(true);
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);
	private AbstractValueFactory<IntervalSetElement> valueFactory;

	public IntervalSetAnalysis() {
		valueFactory = new IntervalSetElementFactory();
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return null;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initStartState(org.jakstab.cfa.Location)
	 */
	@Override
	public AbstractState initStartState(Location label) {
		return new ValuationState(valueFactory);
	}


	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge, Precision precision) {
		final RTLStatement statement = (RTLStatement)cfaEdge.getTransformer();
		final ValuationState iState = (ValuationState)state;

		return Collections.singleton(statement.accept(new DefaultStatementVisitor<AbstractState>() {
			
			@Override
			protected AbstractState visitDefault(RTLStatement stmt) {
				return state;
			}

			@Override
			public AbstractState visit(RTLVariableAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				post.setVariableValue((RTLVariable)lhs, evaledRhs);
				return post;
			}
			
			@Override
			public AbstractState visit(RTLMemoryAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				RTLMemoryLocation m = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
				post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
				return post;
			}

			@Override
			public AbstractState visit(RTLAssume stmt) {
				
				ValuationState post = new ValuationState(iState);
				
				RTLExpression assumption = stmt.getAssumption();
				
				// TODO: implement assume
				
//				if (assumption instanceof RTLOperation) {
//					RTLOperation op = (RTLOperation)assumption;
//					switch (op.getOperator()) {
//					case UNSIGNED_LESS_OR_EQUAL:
//						RTLExpression lhs = op.getOperands()[0];
//						RTLExpression rhs = op.getOperands()[1];
//						IntervalSetElement evaledLhs = (IntervalSetElement)iState.abstractEval(lhs);
//						IntervalSetElement evaledRhs = (IntervalSetElement)iState.abstractEval(rhs);
//
//						if (evaledRhs.getLeft() >= 0) {
//							IntervalElement uLessInt = new IntervalElement(
//									evaledRhs.getRegion(), 0, 
//									evaledRhs.getRight(), 1, evaledLhs.getBitWidth()
//							);
//							// TODO: Implement meet for interval elements for optimal result
//							// uLessInt = uLessInt.meet(evaledLhs);
//							// if uLessInt.isBot() return Collections.emptySet();
//							// cheap but sound solution for now: only use new interval if it has less elements
//							if (uLessInt.size() < evaledLhs.size()) {
//								if (lhs instanceof RTLVariable) {
//									post.setVariableValue((RTLVariable)lhs, uLessInt);
//								} else if (lhs instanceof RTLMemoryLocation) {
//									RTLMemoryLocation m = (RTLMemoryLocation)lhs;
//									AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
//									post.setMemoryValue(evaledAddress, m.getBitWidth(), uLessInt);
//								}
//							}
//						}
//						break;
//					}
//				}

				return post;
			}

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
				
				IntervalSetElement basePointer = new IntervalSetElement(newRegion, 
						ExpressionFactory.createNumber(0, 32));
				
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
			public AbstractState visit(RTLHavoc stmt) {
				ValuationState post = new ValuationState(iState);
				
				// Only create a single state with the havoc range, since this analysis
				// is not path sensitive
				post.setVariableValue(stmt.getVariable(), 
						//new IntervalElement(ExpressionFactory.getInstance().createNumber(0, stmt.getVariable().getBitWidth()), 
								//(RTLNumber)stmt.getMaximum()));
						new IntervalElement(MemoryRegion.GLOBAL, 0, ((RTLNumber)stmt.getMaximum()).longValue(), 1, 
								stmt.getVariable().getBitWidth())
						);
				
				return post;
			}

			@Override
			public AbstractState visit(RTLUnknownProcedureCall stmt) {
				ValuationState post = new ValuationState(iState);
				for (RTLVariable var : stmt.getDefinedVariables()) {
					post.setVariableValue(var, IntervalElement.getTop(var.getBitWidth()));
				}
				post.setMemoryValue(IntervalElement.getTop(Program.getProgram().getArchitecture().getAddressBitWidth()), 
						32, IntervalElement.getTop(32));
				return post;
			}
			
		}));
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		return s;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#merge(org.jakstab.analysis.AbstractState, org.jakstab.analysis.AbstractState)
	 */
	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		return s1.join(s2);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		for(AbstractState state : reached){
			if(s.lessOrEqual(state)){
				return true;
			}
		}
		
		return false;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		// TODO Auto-generated method stub
		return new Pair<AbstractState, Precision>(s,precision);
	}
}
