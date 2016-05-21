package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
import org.jakstab.analysis.newIntervals.statistic.Statistic;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Lattices;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import java.util.Collections;
import java.util.Set;

import static org.jakstab.analysis.newIntervals.IntervalElement.*;

@SuppressWarnings("Unused")
public class IntervalAnalysis implements ConfigurableProgramAnalysis {

	public static JOption<Integer> threshold = JOption.create("interval-threshold", "k", 3, "Sets the threshold used in merge and prec for intervals.");

    public static void register(AnalysisProperties p) {
        p.setShortHand('j');
        p.setName("Signedness Agnostic Interval analysis");
        p.setDescription("Compute intervals without sign information.");
        p.setExplicit(true);
    }

    private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    public IntervalAnalysis() {
		Statistic.activateStatistic();
		logger.debug("Started new interval analysis");
    }

    @Override
    public Precision initPrecision(Location location, StateTransformer transformer) {
		logger.debug("Initialized precision");
        return new IntervalPrecision();
    }

    @Override
    public AbstractState initStartState(Location label) {
		logger.debug("Initialized default state");
		return new GenericValuationState<>(IntervalElementFactory.getFactory());
    }

    @Override
	@SuppressWarnings("unchecked")
    public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		//states equal? s2 is old state (comes from reachedSet)
		if(s2.lessOrEqual(s1)) {
			return s1;
		}
		IntervalPrecision p = (IntervalPrecision) precision;
		if (p.getCount() >= threshold.getValue()) {
			//widen
			logger.verbose("Will widen now");
			return ((GenericValuationState<IntervalElement>) s1).widen((GenericValuationState<IntervalElement>) s2);
		} else {
			return CPAOperators.mergeJoin(s1, s2, precision);
		}
    }

    @Override
	@SuppressWarnings("unchecked")
    public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision) {
		return abstractPost((RTLStatement) cfaEdge.getTransformer(), (GenericValuationState<IntervalElement>) state);
   }

	private static GenericValuationState<IntervalElement> assumeNeq(RTLExpression arg, IntervalElement newInt, GenericValuationState<IntervalElement> newState) {
		if (arg instanceof RTLVariable) {
			if (newInt.hasUniqueConcretization()) {
				BitNumber val = newInt.getUniqueConcretization();
				RTLVariable var = (RTLVariable) arg;
				Pair<AbstractDomain<IntervalElement>, MemoryRegion> oldVal = newState.getVariableValue(var);
				IntervalElement oldInt = oldVal.getLeft().abstractGet();
				oldInt.assertCompatible(newInt);
				if (oldInt.isBot()) {
					// do nothing, is already bottom
					logger.debug("Can not use " + arg + " != " + newInt + ", " + arg + " is BOT");
				} else if (oldInt.isTop()) {
					// can be anything... but we know it is NOT newInt
					newState.setVariableValue(var, newInt.invert(), oldVal.getRight());
				} else if (val.equals(oldInt.minBits)) {
					IntervalElement newInfo = interval(oldInt.minBits.inc(), oldInt.maxBits);
					newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
				} else if (val.equals(oldInt.maxBits)) {
					IntervalElement newInfo = interval(oldInt.minBits, oldInt.maxBits.dec());
					newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
				} else {
					logger.debug("Can not use information in " + arg + ' ' + oldInt + " != " + newInt);
				}
			}
		} else if (arg instanceof RTLOperation) {
			RTLOperation e = (RTLOperation) arg;
			RTLExpression[] args = e.getOperands();
			switch (e.getOperator()) {
				case NEG:
					assert args.length == 1;
					newState = assumeNeq(args[0], newInt.negate(), newState);
					break;
				case NOT:
					assert args.length == 1;
					newState = assumeNeq(args[0], newInt.not(), newState);
					break;
				default:
					logger.warn("Ignoring equality in operation: " + arg + " != " + newInt);
			}
		} else if (arg instanceof RTLNumber) {
			logger.debug("Ignoring equality with constant: " + arg + " != " + newInt);
		} else {
			logger.warn("Ignoring equality: " + arg + " != " + newInt);
		}
		return newState;
	}


	private static GenericValuationState<IntervalElement> assumeEq(RTLExpression arg, IntervalElement newInt, GenericValuationState<IntervalElement> newState) {
		if (arg instanceof RTLVariable) {
			RTLVariable var = (RTLVariable) arg;
			Pair<AbstractDomain<IntervalElement>, MemoryRegion> oldVal = newState.getVariableValue(var);
			IntervalElement oldInt = oldVal.getLeft().abstractGet();
			newState.setVariableValue(var, oldInt.meet(newInt), oldVal.getRight());
		} else if (arg instanceof RTLOperation) {
			RTLOperation e = (RTLOperation) arg;
			RTLExpression[] args = e.getOperands();
			switch (e.getOperator()) {
				case NEG:
					assert args.length == 1;
					newState = assumeEq(args[0], newInt.negate(), newState);
					break;
				case NOT:
					assert args.length == 1;
					newState = assumeEq(args[0], newInt.not(), newState);
					break;
				case PLUS:
					assert args.length > 1;
					IntervalElement[] iArgs = new IntervalElement[args.length];
					for (int i = 0; i < args.length; i++) {
						iArgs[i] = newState.abstractEval(args[i]);
					}
					for (int i = 0; i < args.length; i++) {
						IntervalElement newRes = newInt;
						for (int j = 0; j < args.length; j++) {
							if (i != j) {
								newRes = newRes.sub(iArgs[j]);
							}
						}
						newState = assumeEq(args[i], newRes, newState);
					}
					break;
				default:
					logger.warn("Ignoring equality in operation: " + arg + " == " + newInt);
			}
		} else if (arg instanceof RTLNumber) {
			logger.debug("Ignoring equality with constant: " + arg + " == " + newInt);
		} else {
			logger.warn("Ignoring equality: " + arg + " == " + newInt);
		}
		return newState;
	}

	private static GenericValuationState<IntervalElement> assumeFalse(RTLExpression e, GenericValuationState<IntervalElement> newState) {
		IntervalElement assumeVal = newState.abstractEval(e);
		logger.debug("Assuming " + e + " not to hold");
		assert !assumeVal.isBot() : "Bottoming state reached with " + e + " and " + newState;
		if (assumeVal.hasUniqueConcretization()) {
			assert assumeVal.getUniqueConcretization().zExtLongValue() == 0L : "Infeasible state reached with " + e + " and " + newState;
			logger.verbose(e + " is always false in " + newState);
			return newState;
		}
		if (e instanceof RTLOperation) {
			RTLOperation op = (RTLOperation) e;
			RTLExpression[] args = op.getOperands();
			IntervalElement op0, op1;
			switch (op.getOperator()) {
				case UNKNOWN:
					assert !Options.failFast.getValue() : "Assuming UNKNOWN operator";
					return newState;
				case AND:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = newState.join(assumeFalse(arg, new GenericValuationState<>(newState)));
					}
					return newState;
				case OR:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = assumeFalse(arg, newState);
					}
					return newState;
				case EQUAL:
					assert args.length == 2;
					op0 = newState.abstractEval(args[0]);
					op1 = newState.abstractEval(args[1]);
					newState = assumeNeq(args[0], op1, newState);
					newState = assumeNeq(args[1], op0, newState);
					return newState;
				case LESS:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createLessOrEqual(args[1], args[0]), newState);
				case LESS_OR_EQUAL:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createLessThan(args[1], args[0]), newState);
				case UNSIGNED_LESS:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createUnsignedLessOrEqual(args[1], args[0]), newState);
				case UNSIGNED_LESS_OR_EQUAL:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createUnsignedLessThan(args[1], args[0]), newState);
				case NOT:
					assert args.length == 1;
					newState = assumeTrue(args[0], newState);
					return newState;
				default:
					logger.warn("assumeTrue: Unknown or unhandled operator " + op.getOperator() + " in assumption " + e);
					return newState;
			}
		} else if (e instanceof RTLBitRange) {
			assert !Options.failFast.getValue() : "Assuming a RTLBitRange is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLConditionalExpression) {
			RTLConditionalExpression c = (RTLConditionalExpression) e;
			RTLExpression cond = c.getCondition();
			RTLExpression negCond = ExpressionFactory.createNot(cond);
			RTLExpression t = c.getTrueExpression();
			RTLExpression f = c.getFalseExpression();
			return assumeFalse(ExpressionFactory.createOr(ExpressionFactory.createAnd(cond, t),ExpressionFactory.createAnd(negCond, f)), newState);
		} else if (e instanceof RTLMemoryLocation) {
			RTLMemoryLocation m = (RTLMemoryLocation) e;
			newState.setMemoryValue(m, FALSE_INTERVAL);
			return newState;
		} else if (e instanceof RTLNondet) {
			// this does not really help, but well...
			return newState;
		} else if (e instanceof RTLNumber) {
			throw new AssertionError("Number did not reduce to a constant: " + e);
		} else if (e instanceof RTLSpecialExpression) {
			assert !Options.failFast.getValue() : "Assuming a RTLSpecialExpression is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLVariable) {
			RTLVariable v = (RTLVariable) e;
			newState.setVariableValue(v, FALSE_INTERVAL, newState.getVariableValue(v).getRight());
			return newState;
		} else {
			throw new AssertionError("Unknown assumption " + e);
		}
	}

	private static GenericValuationState<IntervalElement> assumeTrue(RTLExpression e, GenericValuationState<IntervalElement> newState) {
		IntervalElement assumeVal = newState.abstractEval(e);
		logger.debug("Assuming " + e + " to hold");
		assert !assumeVal.isBot() : "Bottoming state reached with " + e + " and " + newState;
		if (assumeVal.hasUniqueConcretization()) {
			assert assumeVal.getUniqueConcretization().zExtLongValue() != 0L : "Infeasible state reached with " + e + " and " + newState;
			logger.verbose(e + " is always true in " + newState);
			return newState;
		}
		if (e instanceof RTLOperation) {
			RTLOperation op = (RTLOperation) e;
			RTLExpression[] args = op.getOperands();
			IntervalElement op0, op1;
			Pair<IntervalElement, IntervalElement> tmp;
			RTLExpression leq, eq;
			switch (op.getOperator()) {
				case UNKNOWN:
					assert !Options.failFast.getValue() : "Assuming UNKNOWN operator";
					return newState;
				case AND:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = assumeTrue(arg, newState);
					}
					return newState;
				case OR:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = newState.join(assumeTrue(arg, new GenericValuationState<>(newState)));
					}
					return newState;
				case EQUAL:
					assert args.length == 2;
					op0 = newState.abstractEval(args[0]);
					op1 = newState.abstractEval(args[1]);
					newState = assumeEq(args[0], op1, newState);
					newState = assumeEq(args[1], op0, newState);
					return newState;
				case LESS:
					assert args.length == 2;
					leq = ExpressionFactory.createLessOrEqual(args[0], args[1]);
					eq = ExpressionFactory.createEqual(args[0], args[1]);
					return assumeTrue(ExpressionFactory.createAnd(leq, ExpressionFactory.createNot(eq)), newState);
				case LESS_OR_EQUAL:
					assert args.length == 2;
					op0 = newState.abstractEval(args[0]);
					op1 = newState.abstractEval(args[1]);
					tmp = IntervalElement.assumeSLeq(op0, op1);
					newState = assumeEq(args[0], tmp.getLeft(), newState);
					newState = assumeEq(args[1], tmp.getRight(), newState);
					return newState;
				case UNSIGNED_LESS:
					assert args.length == 2;
					leq = ExpressionFactory.createUnsignedLessOrEqual(args[0], args[1]);
					eq = ExpressionFactory.createEqual(args[0], args[1]);
					return assumeTrue(ExpressionFactory.createAnd(leq, ExpressionFactory.createNot(eq)), newState);
				case UNSIGNED_LESS_OR_EQUAL:
					assert args.length == 2;
					op0 = newState.abstractEval(args[0]);
					op1 = newState.abstractEval(args[1]);
					tmp = IntervalElement.assumeULeq(op0, op1);
					newState = assumeEq(args[0], tmp.getLeft(), newState);
					newState = assumeEq(args[1], tmp.getRight(), newState);
					return newState;
				case NOT:
					assert args.length == 1;
					newState = assumeFalse(args[0], newState);
					return newState;
				default:
					logger.warn("assumeTrue: Unknown or unhandled operator " + op.getOperator() + " in assumption " + e);
					return newState;
			}
		} else if (e instanceof RTLBitRange) {
			assert !Options.failFast.getValue() : "Assuming a RTLBitRange is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLConditionalExpression) {
			RTLConditionalExpression c = (RTLConditionalExpression) e;
			RTLExpression cond = c.getCondition();
			RTLExpression negCond = ExpressionFactory.createNot(cond);
			RTLExpression t = c.getTrueExpression();
			RTLExpression f = c.getFalseExpression();
			return assumeTrue(ExpressionFactory.createOr(ExpressionFactory.createAnd(cond, t),ExpressionFactory.createAnd(negCond, f)), newState);
		} else if (e instanceof RTLMemoryLocation) {
			RTLMemoryLocation m = (RTLMemoryLocation) e;
			newState.setMemoryValue(m, TRUE_INTERVAL);
			return newState;
		} else if (e instanceof RTLNondet) {
			// this does not really help, but well...
			return newState;
		} else if (e instanceof RTLNumber) {
			throw new AssertionError("Number did not reduce to a constant: " + e);
		} else if (e instanceof RTLSpecialExpression) {
			assert !Options.failFast.getValue() : "Assuming a RTLSpecialExpression is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLVariable) {
			RTLVariable v = (RTLVariable) e;
			newState.setVariableValue(v, TRUE_INTERVAL, newState.getVariableValue(v).getRight());
			return newState;
		} else {
			throw new AssertionError("Unknown assumption " + e);
		}
	}

	public static Set<AbstractState> abstractPost(final RTLStatement statement, final GenericValuationState<IntervalElement> s) {
		logger.info("start processing abstractPost(" + statement + ") " + statement.getLabel());

		Set<AbstractState> res = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				logger.verbose("Found RTLVariableAssignment: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				RTLVariable v = stmt.getLeftHandSide();
				IntervalElement rhs = s.abstractEval(stmt.getRightHandSide());
				MemoryRegion region = newState.getRegion(stmt.getRightHandSide());
				newState.setVariableValue(v, rhs, region);
				logger.verbose("Set " + v + " = " + rhs + " and new region " + region);
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				logger.verbose("Found RTLMemoryAssignment: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				IntervalElement rhs = s.abstractEval(stmt.getRightHandSide());
				newState.setMemoryValue(stmt.getLeftHandSide(), rhs);
				logger.verbose("Set [" + stmt.getLeftHandSide() + "] = " + rhs);
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				logger.verbose("Found RTLAssume: " + stmt);
				RTLExpression e = stmt.getAssumption();
				GenericValuationState<IntervalElement> newState = assumeTrue(e, new GenericValuationState<>(s));
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				logger.verbose("Found RTLAlloc: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				Writable lhs = stmt.getPointer();
				MemoryRegion newRegion;

				// Check for hardcoded allocation names (i.e., stack or FS)
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					newRegion = MemoryRegion.create("alloc" + stmt.getLabel() + '#' + newState.allocationCounter.countAllocation(stmt.getLabel()));
				}
				logger.verbose("Allocated region " + newRegion);

				// We also allow pointers of less than the actual address size, to emulate the 16 bit segment registers FS/GS
				// FS gets a value of (FS, 0) in the prologue.

				if (lhs instanceof RTLVariable) {
					newState.setVariableValue((RTLVariable)lhs, IntervalElement.number(0L, lhs.getBitWidth()), newRegion);
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					IntervalElement abstractAddress = newState.abstractEval(m);
					newState.setMemoryValue(abstractAddress, IntervalElement.number(0L, lhs.getBitWidth()), newRegion);
				}

				return Collections.singleton((AbstractState)newState);
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				logger.verbose("Found RTLDealloc: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				IntervalElement abstractAddress = newState.abstractEval(stmt.getPointer());

				// if the address cannot be determined, set all store memory to TOP
				if (abstractAddress.isTop()) {
					logger.info(newState + ": Cannot resolve location of deallocated memory pointer " + stmt.getPointer() + ". Defaulting ALL memory to TOP!");
					newState.store.setTop();
				} else {
					MemoryRegion region = newState.getRegion(stmt.getPointer());
					if (region.equals(MemoryRegion.GLOBAL) || region.equals(MemoryRegion.STACK)) {
						throw new UnknownPointerAccessException("Cannot deallocate " + region + '!');
					}
					logger.verbose(stmt.getLabel() + ": Dealloc on " + region);
					newState.store.setTop(region);
				}
				return Collections.singleton((AbstractState)newState);
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				logger.warn("Found RTLUnknownProcedureCall: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				for (RTLVariable var : stmt.getDefinedVariables()) {
					newState.setVariableValue(var, top(var.getBitWidth()), newState.getRegion(var));
				}
				newState.store.setTop();
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				logger.warn("Found RTLHavoc: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				RTLVariable var = stmt.getVariable();
				newState.setVariableValue(var, IntervalElement.top(var.getBitWidth()), newState.getVariableValue(var).getRight());
				return Collections.singleton((AbstractState) assumeTrue(ExpressionFactory.createUnsignedLessOrEqual(var, stmt.getMaximum()), newState));
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				logger.verbose("Found RTLMemset: " + stmt);
				IntervalElement value = s.abstractEval(stmt.getValue());
				IntervalElement count = s.abstractEval(stmt.getCount());
				logger.verbose("MemSet(dst: " + stmt.getDestination()+ ", val: " + value + ", count: " + count + ')');
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				if (count.hasUniqueConcretization()) {
					for (long i = 0L; i < count.getUniqueConcretization().zExtLongValue(); i++) {
						RTLExpression off = ExpressionFactory.createNumber(i, count.getBitWidth());
						RTLMemoryLocation pos = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(stmt.getDestination(), off), 8);
						newState.setMemoryValue(pos, value);
					}
				} else {
					assert !Options.failFast.getValue() : "Memset with unknown count parameter: " + count;
					newState = new GenericValuationState<>(IntervalElementFactory.getFactory());
				}
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				logger.verbose("Found RTLMemcpy: " + stmt);
				IntervalElement size = s.abstractEval(stmt.getSize());
				logger.verbose("RTLMemcpy(src: " + stmt.getSource() + ", dst: " + stmt.getDestination() + ", size: " + size + ')');
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				if (size.hasUniqueConcretization()) {
					for (long i = 0L; i < size.getUniqueConcretization().zExtLongValue(); i++) {
						RTLExpression off = ExpressionFactory.createNumber(i, size.getBitWidth());
						RTLMemoryLocation srcPos = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(stmt.getSource(), off), 8);
						RTLMemoryLocation dstPos = ExpressionFactory.createMemoryLocation(ExpressionFactory.createPlus(stmt.getDestination(), off), 8);
						IntervalElement value = newState.getMemoryValue(srcPos);
						newState.setMemoryValue(dstPos, value);
					}
				} else {
					assert !Options.failFast.getValue() : "Memcpy with unknown size parameter: " + size;
					newState = new GenericValuationState<>(IntervalElementFactory.getFactory());
				}
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				logger.warn("Found RTLStatement: " + stmt);
				assert !Options.failFast.getValue() : "Unknown statement: " + stmt;
				return Collections.singleton((AbstractState) new GenericValuationState<>(IntervalElementFactory.getFactory()));
			}
		});

		logger.verbose("finished abstractPost(" + statement + ") in state: " + s + " with result: " + res);
		return res;
	}

    @Override
	@SuppressWarnings("unchecked")
    public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
                                    CFAEdge cfaEdge, Precision precision) {
		logger.debug("Strengthening " + s + " at edge " + cfaEdge + " with precision " + precision);
		boolean couldStrengthen = false;
		for (AbstractState other : otherStates) {
			logger.debug("  With state (" + other.getClass() + ") " + other);
			couldStrengthen |= other instanceof GenericValuationState && ((GenericValuationState<IntervalElement>)other).id != ((GenericValuationState<IntervalElement>)s).id;
		}
		assert !couldStrengthen : "Could actually strengthen here";
        return s; //TODO actually implement something
    }

    @Override
	@SuppressWarnings("unchecked")
    public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		logger.debug("Incrementing precision in " + s + " from " + precision);
		logger.debug("prec((" + s + "), (" + precision + "), (" + reached + ")) called");
		IntervalPrecision p = (IntervalPrecision) precision;
		GenericValuationState<IntervalElement> newState = (GenericValuationState<IntervalElement>) s;
		boolean changed = false;
		for (AbstractState state : reached) {
			GenericValuationState<IntervalElement> rState = (GenericValuationState<IntervalElement>) state;
			changed = changed || rState.lessOrEqual(newState);
		}
		if (!changed) {
			logger.debug("Nothing changing in " + s + " with " + reached);
			return Pair.create(s, (Precision) p.inc());
		}
		else if(p.getCount() >= threshold.getValue()){
			logger.debug("Will Widen Now");
			GenericValuationState<IntervalElement> result = new GenericValuationState<>(newState);
			for (AbstractState state : reached) {
				result = result.widen((GenericValuationState<IntervalElement>) state);
			}
			logger.debug("Widen result: " + result);
			return Pair.create((AbstractState) result, (Precision) new IntervalPrecision());
		} else {
			logger.debug("Incrementing to " + p.inc());
			return Pair.create(s, (Precision) p.inc());
		}
    }

    @Override
    public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		boolean stop = CPAOperators.stopJoin(s, reached, precision);
		logger.debug("Stop-Join for state " + s +
				"\t\nwith reached set " + reached +
				"\t\nempty = " + reached.isEmpty() +
				"\t\nand joinAll = " + Lattices.joinAll(reached) +
				"\t\nand precision " + precision +
				"\t\nresult = " + stop);
        return stop;
    }
}
