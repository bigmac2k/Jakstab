package org.jakstab.analysis.explicit;

import java.util.Collections;
import java.util.Map;
import java.util.Set;

import org.jakstab.Program;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractStore;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.UnknownPointerAccessException;
import org.jakstab.analysis.VariableValuation;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.ExpressionVisitor;
import org.jakstab.rtl.expressions.Operator;
import org.jakstab.rtl.expressions.RTLBitRange;
import org.jakstab.rtl.expressions.RTLConditionalExpression;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNondet;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLOperation;
import org.jakstab.rtl.expressions.RTLSpecialExpression;
import org.jakstab.rtl.expressions.RTLVariable;
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
import org.jakstab.util.Sets;
import org.jakstab.util.Tuple;
import org.jakstab.util.Logger;

public class BDDState implements AbstractState {
	
	private BDDState(VariableValuation<BDDSet> vartable, PartitionedMemory<BDDSet> memtable, AllocationCounter counter) {
		this.abstractVarTable = vartable;
		this.abstractMemoryTable = memtable;
		this.allocationCounter = counter;
	}
	
	protected BDDState(BDDState proto) {
		this(new VariableValuation<BDDSet>(proto.abstractVarTable),
			 new PartitionedMemory<BDDSet>(proto.abstractMemoryTable),
			 AllocationCounter.create());
	}
	
	public BDDState() {
		this(new VariableValuation<BDDSet>(new BDDSetFactory()), new PartitionedMemory<BDDSet>(new BDDSetFactory()), AllocationCounter.create());
	}
	
	private final VariableValuation<BDDSet> abstractVarTable;
	private final PartitionedMemory<BDDSet> abstractMemoryTable;
	private final AllocationCounter allocationCounter;
	
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
		else return "Var = " + abstractVarTable.toString() + ", " + abstractMemoryTable.toString();
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

		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			BDDSet aValue = abstractEval(expressions[i]);
			if(aValue.isTop()) {
				cValues.set(i, RTLNumber.ALL_NUMBERS);
			} else {
				//XXX limit up to k
				logger.debug("limit needed for: " + aValue + " with " + aValue.getSet().sizeBigInt() + " elements");
				cValues.set(i, aValue.concretize());
			}
		}
		return Sets.crossProduct(cValues);
	}
	
	@Override
	public BDDState join(LatticeElement l) {
		BDDState that = (BDDState) l;
		
		if (isTop() || that.isBot()) return this;
		if (isBot() || that.isTop()) return that;
			
		VariableValuation<BDDSet> newVarVal = 
			abstractVarTable.join(that.abstractVarTable); 
		PartitionedMemory<BDDSet> newStore = 
			abstractMemoryTable.join(that.abstractMemoryTable);
		AllocationCounter newAllocCounters = 
				allocationCounter.join(that.allocationCounter);
		
		return new BDDState(newVarVal, newStore, newAllocCounters);
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
	
	public BDDSet getValue(RTLVariable var) {
		return abstractVarTable.get(var);
	}
	
	public void setValue(RTLVariable var, BDDSet value) {
		abstractVarTable.set(var, value);
	}
	
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
			for(RTLNumber rtlnum : pointer.getSet().java()) {
				// XXX SCM why the bitWidth - is contained in rtlnum and in BDDSet.singleton... - CHECK!
				abstractMemoryTable.set(region, rtlnum.longValue(), bitWidth, value);
			}
			return pointer.isSingleton();
		}
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
					for(int i = 1; i < e.getOperandCount(); i++) {
						if(this.region == MemoryRegion.GLOBAL)
							this.region = abstractOperands[i].getRegion();
						if((abstractOperands[i].getRegion() != MemoryRegion.GLOBAL && this.region != abstractOperands[i].getRegion())
						|| this.bits != abstractOperands[i].getBitWidth()) {
							logger.debug("Check for Region or BitWidth failed: this.region: " + this.region + ", that.region: " + abstractOperands[i].getRegion() + ", this.bits: " + this.bits + ", that.bits: " + abstractOperands[i].getBitWidth());
							this.ok = false;
							break;
						}
					}
				}
				public boolean getOk() { return ok; }
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
				
				for(int i = 0; i < e.getOperandCount(); i++)
					abstractOperands[i] = e.getOperands()[i].accept(this);
				
				BDDSet op0;
				BDDSet op1;
				BDDSet op2;
				CheckResult check;
								
				switch(e.getOperator()) {
				/* decided to go for code duplication for readability (more separate cases).
				 * also, clone researchers need something meaningful to analyze...
				 */
				case EQUAL:
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
					logger.info("EQUAL: Returning TOP for: (" + op0 + " " + e.getOperator() + " " + op1 + ")");
					return BDDSet.topBW(1);
					/*assert false : "EQUAL called on something crazy!";
					break;*/
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
					return BDDSet.topBW(1);
					/*assert false : "LESS called on something crazy!";
					break;*/
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
					check = new CheckResult(e, abstractOperands);
					if(check.getOk())
						return new BDDSet(op0.getSet().bAnd(op1.getSet()));
					assert false : "AND called on something crazy";
					break;
				case OR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					check = new CheckResult(e, abstractOperands);
					if(check.getOk())
						return new BDDSet(op0.getSet().bOr(op1.getSet()));
					assert false : "OR called on something crazy";
					break;
				case XOR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					check = new CheckResult(e, abstractOperands);
					if(check.getOk())
						return new BDDSet(op0.getSet().bXOr(op1.getSet()));
					assert false : "XOR called on something crazy";
					break;
				case PLUS:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					check = new CheckResult(e, abstractOperands);
					if(check.getOk())
						return new BDDSet(op0.getSet().plus(op1.getSet()), check.getRegion());
					assert false : "PLUS called on something crazy";
					break;
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
				case SHR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bShr(op1.randomElement().intValue()), op0.getRegion());
					assert false : "SHR called on something crazy";
					break;
				case SHL:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bShl(op1.randomElement().intValue()), op0.getRegion());
					assert false : "SHL called on something crazy";
					break;
				case SAR:
					op0 = abstractOperands[0];
					op1 = abstractOperands[1];
					if(op1.hasUniqueConcretization())
						return new BDDSet(op0.getSet().bSar(op1.randomElement().intValue()), op0.getRegion());
					assert false : "SAR not handled";
					break;
				case ROL:
					assert false : "ROL not handled";
					break;
				case ROR:
					assert false : "ROR not handled";
					break;
				case FSIZE:
					assert false : "FSIZE not handled";
					break;
				case MUL:
					assert false : "MUL not handled";
					break;
				case FMUL:
					assert false : "FMUL not handled";
					break;
				case FDIV:
					assert false : "FDIV not handled";
					break;
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
				return null;
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
		assert result.getBitWidth() == e.getBitWidth() : "BitWidth changed during evaluation of " + e + " to " + result;
		return result;
	}
	
	
	public Set<AbstractState> abstractPost(final RTLStatement statement, final Precision precision) {
		logger.info("processing abstractPost(" + statement + ")");
		logger.info("processing in state: " + this.toString());
		//final ExplicitPrecision eprec = (ExplicitPrecision)precision;
				
		return statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {
			
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
				
				post.setValue(lhs, evaledRhs);				
				return Collections.singleton((AbstractState) post);
			}
			
			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				BDDState post = copyThisState();
				BDDSet evaledRhs = abstractEval(stmt.getRightHandSide());
				
				RTLMemoryLocation m = stmt.getLeftHandSide();
				BDDSet abstractAddress = abstractEvalAddress(m);
				
				if(!post.setMemoryValue(abstractAddress, m.getBitWidth(), evaledRhs)) {
					logger.verbose(stmt.getLabel() + ": Cannot precisely resolve memory write to " + m + ".");
					logger.debug("State: " + BDDState.this);
				}
				
				return Collections.singleton((AbstractState) post);
			}
			
			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				logger.info("Found RTLAssume: " + stmt);
				BDDSet truthValue = abstractEval(stmt.getAssumption());
				
				//if truthValue = False -> infeasible
				// else if True -> fine...
				// else work to do!
				if(truthValue.isSingleton()) {
					if(truthValue.lessOrEqual(BDDSet.TRUE)) {
						logger.info("truthValue TRUE for " + stmt + " (" + truthValue + ")");
						return thisState();
					} else {
						logger.info(stmt.getLabel() + ", state ID " + getIdentifier() + ": Transformer " + stmt + " is infeasible.");
						return Collections.emptySet();
					}
				} else {
					//truth value either true or false -> reduction!
					RTLExpression assumption = stmt.getAssumption();
					assumption = assumption.evaluate(getContext());
					
					if(assumption instanceof RTLOperation) {
						RTLOperation operation = (RTLOperation) assumption;
						switch(operation.getOperator()) {
						case EQUAL:
							logger.info("Handling RTLAssume: " + stmt);
							if(operation.getOperands()[0] instanceof RTLVariable
							&& operation.getOperands()[1] instanceof RTLNumber) {
								RTLVariable var = (RTLVariable) operation.getOperands()[0];
								RTLNumber num = (RTLNumber) operation.getOperands()[1];
								BDDState post = copyThisState();
								post.setValue(var, BDDSet.singleton(num));
								return Collections.singleton((AbstractState) post);
							}
							//XXX work
							assert false;
							break;
						}
					}
				}
				logger.info("Ignoring RTLAssume: " + stmt);
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
					for(RTLNumber rtlnum : abstractDestination.getSet().java()) {
						long base = rtlnum.longValue();
						for(long i = base; i < base + (count * step); i += step) {
							BDDSet pointer = BDDSet.singleton(abstractDestination.getRegion(), ExpressionFactory.createNumber(i, abstractDestination.getBitWidth()));
							post.setMemoryValue(pointer, abstractValue.getBitWidth(), abstractValue);
						}
					}
				} else {
					logger.debug(stmt.getLabel() + ": Overapproximating memset(" + abstractDestination + ", " + abstractValue + ", " + abstractCount + ")");
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
					logger.debug(stmt.getLabel() + ": Overapproximating memcpy(" + abstractDestination + ", " + abstractDestination + ", " + abstractSize + ")");
					post.abstractMemoryTable.setTop(abstractDestination.getRegion());
				}
				return Collections.singleton((AbstractState) post);
			}
			
			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				return thisState();
			}

		});
	}
	
	

}
