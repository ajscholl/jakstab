package org.jakstab.analysis.newIntervals.test;

import org.jakstab.Options;
import org.jakstab.analysis.newIntervals.Bits;
import org.jakstab.analysis.newIntervals.Interval;
import org.jakstab.analysis.newIntervals.IntervalValuationState;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Logger.Level;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * Test for the interval analysis. Creates some expressions, checks whether they are handled in a sound way and fails otherwise.
 */
public class IntervalTest {

	private static final Logger logger = Logger.getLogger(IntervalTest.class);

	public static void main(String[] args) {
		RTLExpression e1 = numbers(8, -2L, -1L, 0L, 1L, 2L);
		RTLExpression e2 = numbers(8, 16L, 32L, 64L, -128L, -64L);
		RTLExpression e3 = ExpressionFactory.createPlus(e1, e2);
		RTLExpression e4 = ExpressionFactory.createMinus(e1, e2);
		RTLExpression e5 = ExpressionFactory.createMultiply(e1, e2);
		RTLExpression e6 = ExpressionFactory.createAnd(e1, e2);
		RTLExpression e7 = ExpressionFactory.createOr(e1, e2);
		RTLExpression[] es = {e1, e2, e3, e4, e5, e6, e7};
		Options.verbosity.setValue(Level.DEBUG.ordinal());
		logger.info("Running test...");
		for (RTLExpression e : es) {
			testEval(e);
		}
		logger.info("Passed test");
	}

	/**
	 * WordTest the evaluation of a single expression.
	 *
	 * @param e The expression.
	 */
	public static void testEval(RTLExpression e) {
		logger.debug("*** Evaluating " + e + " ***");
		Set<RTLNumber> rs = evalSet(e);
		logger.debug("*** Real results: "  + rs + " ***");
		Interval i = Interval.abstractEval(e, new IntervalValuationState());
		logger.debug("*** Computed interval: " + i + " ***");
		for (RTLNumber r : rs) {
			if (!i.isElement(r)) {
				throw new AssertionError("Analysis unsound! Found " + r + ", which is not an element of " + i + ", but should be. In Expression " + e);
			}
		}
	}

	/**
	 * Create an expression which may yield any of the given numbers.
	 *
	 * @param bitSize Bit-size of the numbers.
	 * @param someLongs The numbers.
	 * @return An expression.
	 */
	public static RTLExpression numbers(int bitSize, long... someLongs) {
		RTLNumber[] someNumbers = new RTLNumber[someLongs.length];
		Bits bits = Bits.fromInt(bitSize);
		for (int i = 0; i < someLongs.length; i++) {
			assert (someLongs[i] & bits.getMask()) == someLongs[i] || (someLongs[i] & ~bits.getMask()) == ~bits.getMask();
			someNumbers[i] = ExpressionFactory.createNumber(someLongs[i], bitSize);
		}
		return numbers(someNumbers);
	}

	/**
	 * Create an expression which may yield any of the given numbers.
	 *
	 * @param someNumbers The numbers to yield.
	 * @return An expression.
	 */
	public static RTLExpression numbers(RTLNumber... someNumbers) {
		assert someNumbers.length > 0;
		RTLExpression result = someNumbers[0];
		for (int i = 1; i < someNumbers.length; i++) {
			result = ExpressionFactory.createConditionalExpression(new RTLNondet(1), result, someNumbers[i]);
		}
		return result;
	}

	/**
	 * Try to deduce all possible values of an expression. Explodes for larger state spaces!
	 *
	 * @param e The expression to reduce.
	 * @return A set of all possible results.
	 */
	private static Set<RTLNumber> evalSet(RTLExpression e) {
		ExpressionVisitor<Set<RTLNumber>> visitor = new ExpressionVisitor<Set<RTLNumber>>() {

			@Override
			public Set<RTLNumber> visit(RTLBitRange e) {
				// TODO handle bit ranges
				throw new UnsupportedOperationException("can not visit bit range");
			}

			@Override
			public Set<RTLNumber> visit(RTLConditionalExpression e) {
				// just evaluate all possible branches
				Set<RTLNumber> cond = evalSet(e.getCondition());
				Set<RTLNumber> result = new FastSet<>();
				for (RTLNumber n : cond) {
					if (n.longValue() == 0L) {
						result.addAll(evalSet(e.getFalseExpression()));
					} else {
						result.addAll(evalSet(e.getTrueExpression()));
					}
				}
				return result;
			}

			@Override
			public Set<RTLNumber> visit(RTLMemoryLocation m) {
				// an memory location can contain anything...
				return evalSet(new RTLNondet(m.getBitWidth()));
			}

			@Override
			public Set<RTLNumber> visit(RTLNondet e) {
				// can contain anything...
				Bits bits = Bits.fromInt(e.getBitWidth());
				assert bits.getBitWidth() <= 8; // larger bit sizes are bad...
				Set<RTLNumber> result = new FastSet<>();
				for (long i = 0L; (i & bits.getMask()) == i; i++) { // TODO this loop is broken for 64 bits
					result.add(ExpressionFactory.createNumber(bits.narrow(i), bits.getBitWidth()));
				}
				return result;
			}

			@Override
			public Set<RTLNumber> visit(RTLNumber e) {
				// this is easy, just make sure we narrow the value to the correct range
				Bits bits = Bits.fromInt(e.getBitWidth());
				return Collections.singleton(ExpressionFactory.createNumber(bits.narrow(e.longValue()), bits.getBitWidth()));
			}

			/**
			 * Instantiate the operation with the given possible list of sets of arguments.
			 *
			 * @param op The operation.
			 * @param args Possible valuations.
			 * @return A list of possible operations.
			 */
			private List<RTLOperation> genOps(RTLOperation op, List<Set<RTLNumber>> args) {
				List<RTLOperation> ops = new ArrayList<>();
				ops.add(op);
				int argNum = 0;
				int len = op.getOperands().length;
				for (Set<RTLNumber> arg : args) {
					List<RTLOperation> newOps = new ArrayList<>();
					for (RTLNumber val : arg) {
						for (RTLOperation thisOp : ops) {
							RTLExpression[] newArgs = new RTLExpression[len];
							System.arraycopy(thisOp.getOperands(), 0, newArgs, 0, len);
							newArgs[argNum] = val;
							RTLOperation newOp = (RTLOperation)ExpressionFactory.createOperation(thisOp.getOperator(), newArgs);
							newOps.add(newOp);
						}
					}
					ops = newOps;
					argNum++;
				}
				return ops;
			}

			@Override
			public Set<RTLNumber> visit(RTLOperation e) {
				List<Set<RTLNumber>> args = new ArrayList<>(e.getOperandCount());
				for (RTLExpression arg : e.getOperands()) {
					args.add(evalSet(arg));
				}
				// just build all possible valuations
				List<RTLOperation> ops = genOps(e, args);
				Set<RTLNumber> result = new FastSet<>();
				for (RTLOperation op : ops) {
					// and then evaluate them
					result.addAll(evalSet(op.evaluate(new Context())));
				}
				return result;
			}

			@Override
			public Set<RTLNumber> visit(RTLSpecialExpression e) {
				// these are strange and not really implemented IMHO
				throw new UnsupportedOperationException("can not visit special expression");
			}

			@Override
			public Set<RTLNumber> visit(RTLVariable e) {
				// a variable can have any value...
				return evalSet(new RTLNondet(e.getBitWidth()));
			}
		};
		Set<RTLNumber> result = e.accept(visitor);
		for (RTLNumber n : result) {
			Bits bits = Bits.fromInt(n.getBitWidth());
			assert n.longValue() == bits.narrow(n.longValue());
		}
		return result;
	}
}
