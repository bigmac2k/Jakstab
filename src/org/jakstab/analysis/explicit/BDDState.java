package org.jakstab.analysis.explicit;

import java.util.Set;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.VariableValuation;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.ExpressionVisitor;
import org.jakstab.rtl.expressions.RTLBitRange;
import org.jakstab.rtl.expressions.RTLConditionalExpression;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNondet;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLOperation;
import org.jakstab.rtl.expressions.RTLSpecialExpression;
import org.jakstab.rtl.expressions.RTLVariable;
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
import org.jakstab.util.Tuple;

public class BDDState implements AbstractState {
	
	private BDDState(VariableValuation<BDDSet> vartable, PartitionedMemory<BDDSet> memtable) {
		this.abstractVarTable = vartable;
		this.abstractMemoryTable = memtable;
	}
	
	private final VariableValuation<BDDSet> abstractVarTable;
	private final PartitionedMemory<BDDSet> abstractMemoryTable;

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		// TODO Auto-generated method stub
		BDDState that = (BDDState) l;
		return false;
	}

	@Override
	public boolean isTop() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public boolean isBot() {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(
			RTLExpression... expressions) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractState join(LatticeElement l) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Location getLocation() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public String getIdentifier() {
		// TODO Auto-generated method stub
		return null;
	}
	
	/*None Interface Methods - called in BDDAddressTracking
	 * See BasedNumberValuation for similar structure.
	 */
	
	private BDDSet abstractEvalAddress(RTLMemoryLocation m) {
		BDDSet abstractAddress = abstractEval(m.getAddress());
		//Segment register is some special x86 magic
		RTLExpression segmentReg = m.getSegmentRegister();
		if(segmentReg != null) {
			if(abstractAddress.getRegion() != MemoryRegion.GLOBAL)
				return BDDSet.topBW(m.getBitWidth());
			BDDSet segmentValue = abstractEval(segmentReg);
			assert segmentValue.isSingleton() && segmentValue.randomElement().intValue() == 0 : "Segment " + segmentReg + " has been assigned a value!";
			abstractAddress = new BDDSet(abstractAddress.getSet(), segmentValue.getRegion());
		}
		return abstractAddress;
	}
	
	private BDDSet getMemoryValue(BDDSet pointer, int bitWidth) {
		//XXX like in the original - if pointer.getRegion() == MemoryRegion.TOP -> assert false...
		if(pointer.isTop() || pointer.getSet().isFull())
			return BDDSet.topBW(bitWidth);
		assert pointer.getRegion() != MemoryRegion.TOP : "Pointer deref with TOP region";
		//the following is again essentially a fold1...
		BDDSet result = null;
		for(RTLNumber rtlnum : pointer.getSet().java()) {
			BDDSet values = abstractMemoryTable.get(pointer.getRegion(), rtlnum.intValue(), rtlnum.getBitWidth());
			if(result == null)
				result = BDDSet.empty(values.getBitWidth(), values.getRegion());
			assert values.getBitWidth() == result.getBitWidth() : "Try to union different bitwidths at pointer deref";
			if(values.getRegion() != result.getRegion())
				return BDDSet.topBW(result.getBitWidth());
			result = new BDDSet(result.getSet().union(values.getSet()), result.getRegion());
		}
		return result;
	}
	
	BDDSet abstractEval(RTLExpression e) {
		ExpressionVisitor<BDDSet> visitor = new ExpressionVisitor<BDDSet>() {
			
			@Override
			public BDDSet visit(RTLBitRange e) {
				BDDSet abstractFirst = e.getFirstBitIndex().accept(this);
				BDDSet abstractLast = e.getLastBitIndex().accept(this);
				BDDSet abstractOperand = e.getOperand().accept(this);
				
				if(!(abstractFirst.hasUniqueConcretization() && abstractLast.hasUniqueConcretization()))
					return BDDSet.topBW(e.getBitWidth());
				return abstractOperand.bitExtract(abstractFirst.randomElement().intValue(), abstractLast.randomElement().intValue());
			}
			
			@Override
			public BDDSet visit(RTLConditionalExpression e) {
				BDDSet abstractCondition = e.getCondition().accept(this);
				BDDSet result = BDDSet.empty(e.getBitWidth());
				if(BDDSet.TRUE.lessOrEqual(abstractCondition)) {
					BDDSet abstractTrue = e.getTrueExpression().accept(this);
					result = result.join(abstractTrue);
				}
				if(BDDSet.FALSE.lessOrEqual(abstractCondition)) {
					BDDSet abstractFalse = e.getFalseExpression().accept(this);
					result = result.join(abstractFalse);
				}
				return result;
			}

			@Override
			public BDDSet visit(RTLMemoryLocation m) {
				//XXX restrict to n values
				return getMemoryValue(abstractEval(m), m.getBitWidth());
			}

			@Override
			public BDDSet visit(RTLNondet e) {
				return BDDSet.topBW(e.getBitWidth());
			}

			@Override
			public BDDSet visit(RTLNumber e) {
				return BDDSet.singleton(e);
			}

			@Override
			public BDDSet visit(RTLOperation e) {
				BDDSet[] abstractOperands = new BDDSet[e.getOperandCount()];
				
				for(int i = 0; i < e.getOperandCount(); i++)
					abstractOperands[i] = e.getOperands()[i].accept(this);
				
				BDDSet op0 = abstractOperands[0];
				BDDSet op1 = abstractOperands[1];
				BDDSet op2 = abstractOperands[2];
								
				switch(e.getOperator()) {
				//decided to go for code duplication for readability (more separate cases).
				case EQUAL:
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
					if(!op0.isTop()
					&& !op1.isTop()
					&& op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth()) {
						BDDSet result = BDDSet.empty(1);
						if(!op0.getSet().intersect(op1.getSet()).isEmpty())
							result = result.join(BDDSet.TRUE);
						if(!op0.getSet().invert().intersect(op1.getSet()).isEmpty())
							result = result.join(BDDSet.FALSE);
						assert !result.getSet().isEmpty() : "Equal produced no result!?";
						return result;
					}
					assert false : "EQUAL called on something crazy!";
					break;
				case UNSIGNED_LESS:
				case LESS:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(!op0.isTop()
					&& !op1.isTop()
					&& !op0.getSet().isEmpty()
					&& !op1.getSet().isEmpty()
					&& op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth()) {
						BDDSet result = BDDSet.empty(1);
						if(op0.getSet().min().longValue() < op1.getSet().max().longValue())
							result = result.join(BDDSet.TRUE);
						if(op0.getSet().max().longValue() >= op1.getSet().min().longValue())
							result = result.join(BDDSet.FALSE);
						return result;
					}
					assert false : "LESS called on something crazy!";
					break;
				case UNSIGNED_LESS_OR_EQUAL:
				case LESS_OR_EQUAL:
					//== and <
					RTLExpression eLess = ExpressionFactory.createLessThan(e.getOperands()[0], e.getOperands()[1]);
					RTLExpression eEqual = ExpressionFactory.createEqual(e.getOperands()[0], e.getOperands()[1]);
					BDDSet less = eLess.accept(this);
					BDDSet equal = eEqual.accept(this);
					return less.join(equal);
				case NOT:
					return new BDDSet(abstractOperands[0].getSet().bNot());
				case NEG:
					return new BDDSet(abstractOperands[0].getSet().negate());
				case AND:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth())
						return new BDDSet(op0.getSet().bAnd(op1.getSet()));
					assert false : "AND called on something crazy";
					break;
				case OR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth())
						return new BDDSet(op0.getSet().bOr(op1.getSet()));
					assert false : "OR called on something crazy";
					break;
				case XOR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth())
						return new BDDSet(op0.getSet().bXOr(op1.getSet()));
					assert false : "XOR called on something crazy";
					break;
				case PLUS:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op0.getRegion() == op1.getRegion()
					&& op0.getBitWidth() == op1.getBitWidth())
						return new BDDSet(op0.getSet().plus(op1.getSet()), MemoryRegion.GLOBAL);
					assert false : "PLUS called on something crazy";
					break;
				case UNKNOWN:
				case CAST:
				case SIGN_EXTEND:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					op2 = abstractOperands[2];
					if(op0.hasUniqueConcretization()
					&& op1.hasUniqueConcretization())
						return op2.signExtend(op0.randomElement().intValue(), op1.randomElement().intValue());
					assert false : "SIGN_EXTEND called on something crazy";
					break;
				case ZERO_FILL:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					op2 = abstractOperands[2];
					if(op0.hasUniqueConcretization()
					&& op1.hasUniqueConcretization())
						return op2.zeroFill(op0.randomElement().intValue(), op1.randomElement().intValue());
					assert false : "ZERO_FILL called on something crazy";
					break;
				case FSIZE:
				case MUL:
				case FMUL:
				case FDIV:
				case DIV:
				case MOD:
				case POWER_OF:
				case SHR:
				case SAR:
				case SHL:
				case ROL:
				case ROR:
				case ROLC:
				case RORC:
				default:
					assert false : "Operator not handled";
					break;
				}
				System.exit(1);
			}

			@Override
			public BDDSet visit(RTLSpecialExpression e) {
				//XXX todo [SCM] debug printf and possibly getprocaddress... - have a look at RTL definitions
				return BDDSet.topBW(0);
			}

			@Override
			public BDDSet visit(RTLVariable e) {
				return abstractVarTable.get(e);
			}
			
		};
		
		BDDSet result = e.accept(visitor);
		assert result.getBitWidth() == e.getBitWidth() : "BitWidth changed during evaluation of " + e + " to " + result;
		return result;
	}
	
	
	public Set<AbstractState> abstractPost(final RTLStatement statement, final Precision precision) {
		final ExplicitPrecision eprec = (ExplicitPrecision)precision;
		
		return statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {
			
			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				return null;
			}
			
			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				return null;
			}
			
			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				return null;
			}
			
			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				return null;
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				return null;
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				return null;
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				return null;
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				return null;
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				return null;
			}
			
			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				return null;
			}

		});
	}
	
	

}