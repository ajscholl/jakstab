package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.IterableIterator;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap.EntryIterator;
import org.jakstab.util.Pair;

import java.util.Collections;
import java.util.Map.Entry;
import java.util.Set;

import static org.jakstab.analysis.newIntervals.IntervalElement.FALSE_INTERVAL;
import static org.jakstab.analysis.newIntervals.IntervalElement.TRUE_INTERVAL;

@SuppressWarnings("Unused")
public class IntervalAnalysis implements ConfigurableProgramAnalysis {

    public static void register(AnalysisProperties p) {
        p.setShortHand('j');
        p.setName("Signedness Agnostic Interval analysis");
        p.setDescription("Compute intervals without sign information.");
        p.setExplicit(true);
    }

    private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    public IntervalAnalysis() {
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
		if (s2.isTop() || s1.isBot()) {
			return s2;
		}
		if (s1.isTop()) {
			return s1;
		}
		GenericValuationState<IntervalElement> current = (GenericValuationState<IntervalElement>) s1;
		GenericValuationState<IntervalElement> towards = (GenericValuationState<IntervalElement>) s2;

		GenericValuationState<IntervalElement> widenedState = new GenericValuationState<>(IntervalElementFactory.getFactory());

		// Widen variable valuations
		for (Entry<RTLVariable,IntervalElement> entry : new IterableIterator<>(current.variableIterator())) {
			RTLVariable var = entry.getKey();
			IntervalElement v = entry.getValue();
			Pair<AbstractDomain<IntervalElement>, MemoryRegion> vv = towards.getVariableValue(var);
			widenedState.setVariableValue(var, v.widen(vv.getLeft().abstractGet()), vv.getRight());
		}

		// Widen memory
		for (EntryIterator<MemoryRegion, Long, IntervalElement> entryIt = current.storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			IntervalElement v = entryIt.getValue();
			int bitWidth = v.getBitWidth();
			widenedState.setMemoryValue(region, offset, bitWidth, v.widen(towards.getMemoryValue(region, offset, bitWidth)));
		}

		return widenedState;
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
				if (val.equals(oldInt.minBits)) {
					if (val.equals(oldInt.maxBits)) {
						newState.setVariableValue(var, oldInt.bot(), oldVal.getRight());
					} else {
						newState.setVariableValue(var, IntervalElement.interval(oldInt.minBits.inc(), oldInt.maxBits), oldVal.getRight());
					}
				} else if (val.equals(oldInt.maxBits)) {
					newState.setVariableValue(var, IntervalElement.interval(oldInt.minBits, oldInt.maxBits.dec()), oldVal.getRight());
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
		logger.verbose("start processing abstractPost(" + statement + ") " + statement.getLabel());

		Set<AbstractState> res = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				logger.verbose("Found RTLVariableAssignment: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				IntervalElement rhs = s.abstractEval(stmt.getRightHandSide());
				newState.setVariableValue(stmt.getLeftHandSide(), rhs, newState.getVariableValue(stmt.getLeftHandSide()).getRight());
				logger.verbose("Set " + stmt.getLeftHandSide() + " = " + rhs);
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
				logger.verbose("Ignoring RTLAlloc: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				logger.verbose("Ignoring RTLDealloc: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				logger.verbose("Found RTLUnknownProcedureCall: " + stmt);
				assert !Options.failFast.getValue() : "Unknown procedure call: " + stmt;
				return Collections.singleton((AbstractState) new GenericValuationState<>(IntervalElementFactory.getFactory()));
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				logger.verbose("Found RTLHavoc: " + stmt);
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				RTLVariable var = stmt.getVariable();
				newState.setVariableValue(var, IntervalElement.top(var.getBitWidth()), newState.getVariableValue(var).getRight());
				return Collections.singleton((AbstractState) assumeTrue(ExpressionFactory.createUnsignedLessOrEqual(var, stmt.getMaximum()), newState));
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				logger.verbose("Found RTLMemset: " + stmt);
				IntervalElement destination = s.abstractEval(stmt.getDestination());
				IntervalElement value = s.abstractEval(stmt.getValue());
				IntervalElement count = s.abstractEval(stmt.getCount());
				logger.verbose("MemSet(dst: " + destination + ", val: " + value + ", count: " + count + ')');
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				if (count.hasUniqueConcretization()) {
					for (long i = 0L; i < count.getUniqueConcretization().zExtLongValue(); i++) {
						newState.setMemoryValue(destination.add(IntervalElement.number(i, count.getBitWidth())), value);
					}
				} else {
					assert !Options.failFast.getValue() : "Memset with unknown count parameter: " + count;
				}
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				logger.verbose("Found RTLMemcpy: " + stmt);
				IntervalElement source = s.abstractEval(stmt.getSource());
				IntervalElement destination = s.abstractEval(stmt.getDestination());
				IntervalElement size = s.abstractEval(stmt.getSize());
				logger.verbose("RTLMemcpy(src: " + source + ", dst: " + destination + ", size: " + size + ')');
				GenericValuationState<IntervalElement> newState = new GenericValuationState<>(s);
				if (size.hasUniqueConcretization()) {
					for (long i = 0L; i < size.getUniqueConcretization().zExtLongValue(); i++) {
						IntervalElement value = newState.getMemoryValue(source.add(IntervalElement.number(i, size.getBitWidth())), 8);
						newState.setMemoryValue(destination.add(IntervalElement.number(i, size.getBitWidth())), value);
					}
				} else {
					assert !Options.failFast.getValue() : "Memcpy with unknown count parameter: " + size;
				}
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				logger.verbose("Found RTLStatement: " + stmt);
				assert !Options.failFast.getValue() : "Unknown statement: " + stmt;
				return Collections.singleton((AbstractState) new GenericValuationState<>(IntervalElementFactory.getFactory()));
			}
		});

		logger.debug("finished abstractPost(" + statement + ") in state: " + s + " with result: " + res);
		return res;
	}

    @Override
    public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
                                    CFAEdge cfaEdge, Precision precision) {
		logger.debug("Failing to strengthen (not implemented)");
        return s; //TODO actually implement something
    }

    @Override
    public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		logger.debug("Incrementing precision");
		Precision newPrecision = ((IntervalPrecision) precision).inc();
        return Pair.create(s, newPrecision);
    }

    @Override
    public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		logger.debug("Stop-Join");
        return CPAOperators.stopJoin(s, reached, precision);
    }
}
