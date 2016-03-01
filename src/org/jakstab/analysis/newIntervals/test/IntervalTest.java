package org.jakstab.analysis.newIntervals.test;

import org.jakstab.analysis.newIntervals.Bits;
import org.jakstab.analysis.newIntervals.Interval;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.FastSet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;

/**
 * Test for the interval analysis. Creates some expressions, checks whether they are handled in a sound way and fails otherwise.
 */
public class IntervalTest {
	public static void main(String[] args) {
		RTLExpression e1 = numbers(8, -2, -1, 0, 1, 2);
		RTLExpression e2 = numbers(8, 16, 32, 64, -128, -64);
		RTLExpression e3 = ExpressionFactory.createPlus(e1, e2);
		RTLExpression e4 = ExpressionFactory.createMinus(e1, e2);
		RTLExpression e5 = ExpressionFactory.createMultiply(e1, e2);
		RTLExpression e6 = ExpressionFactory.createAnd(e1, e2);
		RTLExpression e7 = ExpressionFactory.createOr(e1, e2);
		RTLExpression[] es = new RTLExpression[] {e1, e2, e3, e4, e5, e6, e7};
		System.out.println("Running test...");
		for (RTLExpression e : es) {
			testEval(e);
		}
		System.out.println("Passed test");
	}

	/**
	 * Test the evaluation of a single expression.
	 *
	 * @param e The expression.
	 */
	public static void testEval(RTLExpression e) {
		System.out.println("Testing " + e);
		Set<RTLNumber> rs = evalSet(e);
		System.out.println("Evaluated set " + rs);
		Interval i = Interval.abstractEval(e);
		for (RTLNumber r : rs) {
			if (!i.isElement(r.longValue())) {
				throw new AssertionError("Analysis unsound! Found " + r + ", which is not an element of " + i + ", but should be. In Expression " + e);
			}
		}
	}

	/**
	 * Create an expression which may yield any of the given numbers.
	 *
	 * @param bitsize Bitsize of the numbers.
	 * @param someLongs The numbers.
	 * @return An expression.
	 */
	public static RTLExpression numbers(int bitsize, long... someLongs) {
		RTLNumber[] someNumbers = new RTLNumber[someLongs.length];
		Bits bits = Bits.fromInt(bitsize);
		for (int i = 0; i < someLongs.length; i++) {
			assert (someLongs[i] & bits.getMask()) == someLongs[i] || ((someLongs[i] & ~bits.getMask()) == ~bits.getMask());
			someNumbers[i] = ExpressionFactory.createNumber(someLongs[i], bitsize);
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
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<RTLNumber> visit(RTLConditionalExpression e) {
				// just evaluate all possible branches
				Set<RTLNumber> cond = evalSet(e.getCondition());
				Set<RTLNumber> result = new FastSet<>();
				for (RTLNumber n : cond) {
					if (n.longValue() == 0) {
						result.addAll(evalSet(e.getFalseExpression()));
					} else {
						result.addAll((evalSet(e.getTrueExpression())));
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
				for (long i = 0; (i & bits.getMask()) == i; i++) { // this loop is broken for 64 bits
					result.add(ExpressionFactory.createNumber(i, bits.getBitWidth()));
				}
				return result;
			}

			@Override
			public Set<RTLNumber> visit(RTLNumber e) {
				// this is easy
				return Collections.singleton(e);
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
				throw new UnsupportedOperationException();
			}

			@Override
			public Set<RTLNumber> visit(RTLVariable e) {
				// a variable can have any value...
				return evalSet(new RTLNondet(e.getBitWidth()));
			}
		};
		return e.accept(visitor);
	}
}