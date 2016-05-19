package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.Options;
import org.jakstab.analysis.AbstractValue;
import org.jakstab.rtl.expressions.*;
import org.jakstab.util.Logger;

import java.util.ArrayList;
import java.util.List;

public final class AbstractEvaluator<T extends AbstractValue & Boxable<T>> {

	private static final Logger logger = Logger.getLogger(AbstractEvaluator.class);

	private final AbstractDomainFactory<T> factory;

	private final AbstractValuationState<T> s;

	public AbstractEvaluator(AbstractDomainFactory<T> factory, AbstractValuationState<T> s) {
		assert factory != null;
		assert s != null;
		this.factory = factory;
		this.s = s;
	}

	public AbstractDomain<T> evalExpression(RTLExpression e) {
		logger.verbose("Evaluating " + e);
		final int bitSize = e.getBitWidth();
		if (bitSize <= 0) {
			// make sure BitRanges supply valid sizes
			throw new IllegalArgumentException("BitWidth smaller than 1 in " + e);
		}
		ExpressionVisitor<AbstractDomain<T>> visitor = new ExpressionVisitor<AbstractDomain<T>>() {

			@Override
			public AbstractDomain<T> visit(RTLBitRange e) {
				logger.debug("Evaluating bit range with " + e.getFirstBitIndex() + " and " + e.getLastBitIndex() + " for operand " + e.getOperand());
				AbstractDomain<T> value = evalExpression(e.getOperand());
				logger.debug("  Evaluated operand to " + value);
				T startBit = evalExpression(e.getFirstBitIndex()).cast(value.getBitWidth()).abstractGet();
				logger.debug("  Evaluated start bit to " + startBit);
				AbstractDomain<T> endBit = evalExpression(e.getLastBitIndex()).cast(value.getBitWidth());
				logger.debug("  Evaluated end bit to " + endBit);
				AbstractDomain<T> one = factory.number(1L, endBit.getBitWidth());
				// (1 << (endBit - startBit + 1) - 1) << startBit
				T mask = one.shl(endBit.sub(startBit).add(one.abstractGet()).abstractGet()).sub(one.abstractGet()).shl(startBit).abstractGet();
				logger.debug("  Computed mask as " + mask);
				AbstractDomain<T> result = value.and(mask).shr(startBit);
				logger.debug("  Computed result as " + result);
				return result.cast(bitSize);
			}

			@Override
			public AbstractDomain<T> visit(RTLConditionalExpression e) {
				AbstractDomain<T> cond = evalExpression(e.getCondition());
				assert cond.getBitWidth() == 1 : "Condition has to be a boolean";
				if (cond.hasUniqueConcretization()) {
					if (cond.getUniqueConcretization().zExtLongValue() != 0L) {
						assert cond.getUniqueConcretization().zExtLongValue() == 1L;
						return evalExpression(e.getTrueExpression());
					}
					return evalExpression(e.getFalseExpression());
				} else {
					AbstractDomain<T> t = evalExpression(e.getTrueExpression());
					AbstractDomain<T> f = evalExpression(e.getFalseExpression());
					return t.join(f);
				}
			}

			@Override
			public AbstractDomain<T> visit(RTLMemoryLocation m) {
				return s.getMemoryValue(m);
			}

			@Override
			public AbstractDomain<T> visit(RTLNondet e) {
				// non-deterministic value, i.e. TOP
				return factory.top(bitSize);
			}

			@Override
			public AbstractDomain<T> visit(RTLNumber e) {
				// a single number, simple
				return factory.number(e);
			}

			@Override
			public AbstractDomain<T> visit(RTLOperation e) {
				RTLExpression[] args = e.getOperands();
				int opSize = e.getBitWidth();
				boolean mayCast = false;
				switch (e.getOperator()) {
					case ROLC:
					case RORC:
					case NOT:
					case NEG:
					case AND:
					case OR:
					case XOR:
					case PLUS:
					case MUL:
					case UDIV:
					case SDIV:
					case UMOD:
					case SMOD:
					case SHR:
					case SAR:
					case SHL:
					case ROL:
					case ROR:
						mayCast = true;
				}
				List<AbstractDomain<T>> iArgs = new ArrayList<>(args.length);
				for (RTLExpression arg : args) {
					AbstractDomain<T> v = evalExpression(arg);
					if (v.getBitWidth() != opSize && mayCast) {
						logger.warn("Casting " + v + " to " + opSize);
						v = v.cast(bitSize);
					}
					iArgs.add(v);
				}
				long w = (long)bitSize;
				AbstractDomain<T> op0, op1, op2;
				switch (e.getOperator()) {
					case UNKNOWN:
						assert !Options.failFast.getValue() : "Evaluated UNKNOWN operator";
						return factory.top(bitSize);
					case FSIZE:
					case FMUL:
					case FDIV:
					case POWER_OF:
					case ROLC:
					case RORC: /* Rotate with carry */
						// we do not support these operations
						logger.debug("Skipping unsupported operation " + e.getOperator());
						return factory.top(bitSize);

					// Operators for changing bit-width
					case CAST:
						assert args.length == 2;
						op0 = iArgs.get(0);
						op1 = iArgs.get(1);
						if (op1.hasUniqueConcretization()) {
							int newBitSize = (int)op1.getUniqueConcretization().zExtLongValue();
							return op0.truncate(newBitSize);
						}
						assert false : "CAST called on something crazy";
						return factory.top(bitSize);
					case SIGN_EXTEND:
					case ZERO_FILL:
						assert e.getOperandCount() == 3 : e.getOperator() + " called with " + e.getOperandCount() + " operands";
						op0 = iArgs.get(0);
						op1 = iArgs.get(1);
						op2 = iArgs.get(2);
						if (op0.hasUniqueConcretization() && op1.hasUniqueConcretization()) {
							switch (e.getOperator()) {
								case SIGN_EXTEND: return op2.signExtend((int)op0.getUniqueConcretization().zExtLongValue(), (int)op1.getUniqueConcretization().zExtLongValue());
								case ZERO_FILL: return op2.zeroExtend((int)op0.getUniqueConcretization().zExtLongValue(), (int)op1.getUniqueConcretization().zExtLongValue());
							}
						}
						assert false : e.getOperator() + " called on something crazy";
						return factory.top(bitSize);

					// Comparison
					case EQUAL:
						assert args.length == 2;
						return iArgs.get(0).eq(iArgs.get(1).abstractGet());
					case LESS:
						assert args.length == 2;
						return iArgs.get(0).signedLessThan(iArgs.get(1).abstractGet());
					case LESS_OR_EQUAL:
						assert args.length == 2;
						return iArgs.get(0).signedLessThanOrEqual(iArgs.get(1).abstractGet());
					case UNSIGNED_LESS:
						assert args.length == 2;
						return iArgs.get(0).unsignedLessThan(iArgs.get(1).abstractGet());
					case UNSIGNED_LESS_OR_EQUAL:
						assert args.length == 2;
						return iArgs.get(0).unsignedLessThanOrEqual(iArgs.get(1).abstractGet());

					// Unary operators
					case NOT:
						assert args.length == 1;
						return iArgs.get(0).not();
					case NEG:
						assert args.length == 1;
						return iArgs.get(0).negate();

					// Associative commutative bitwise arithmetic operators
					case AND:
					case OR:
					case XOR:
					case PLUS:
					case MUL:
						assert args.length >= 2;
						op0 = iArgs.get(0);
						for (int i = 1; i < iArgs.size(); i++) {
							op1 = iArgs.get(i);
							switch (e.getOperator()) {
								case AND:
									op0 = op1.and(op1.abstractGet());
									break;
								case OR:
									op0 = op0.or(op1.abstractGet());
									break;
								case XOR:
									op0 = op0.xor(op1.abstractGet());
									break;
								case PLUS:
									op0 = op0.add(op1.abstractGet());
									break;
								case MUL:
									op0 = op0.mulDouble(op1.abstractGet());
									break;
							}
						}
						return op0;

					// Other bitwise arithmetic operators
					case UDIV:
						assert args.length == 2;
						return iArgs.get(0).unsignedDiv(iArgs.get(1).abstractGet());
					case SDIV:
						assert args.length == 2;
						return iArgs.get(0).signedDiv(iArgs.get(1).abstractGet());
					case UMOD:
						assert args.length == 2;
						return iArgs.get(0).unsignedRem(iArgs.get(1).abstractGet());
					case SMOD:
						assert args.length == 2;
						return iArgs.get(0).signedRem(iArgs.get(1).abstractGet());

					// Bitwise shift operations
					case SHR:
						assert args.length == 2;
						return iArgs.get(0).shr(iArgs.get(1).zeroExtend(bitSize).abstractGet());
					case SAR:
						assert args.length == 2;
						return iArgs.get(0).sar(iArgs.get(1).zeroExtend(bitSize).abstractGet());
					case SHL:
						assert args.length == 2;
						return iArgs.get(0).shl(iArgs.get(1).zeroExtend(bitSize).abstractGet());
					case ROL:
						// a rol b ==> a shl b | a sar (w - b)
						assert args.length == 2;
						op0 = iArgs.get(0);
						op1 = iArgs.get(1).zeroExtend(bitSize);
						op2 = factory.interval(w, w, bitSize); // w
						return op0.shl(op1.abstractGet()).or(op0.sar(op2.sub(op1.abstractGet()).abstractGet()).abstractGet());
					case ROR:
						// a ror b ==> a sar b | a shl (w - b)
						assert args.length == 2;
						op0 = iArgs.get(0);
						op1 = iArgs.get(1).zeroExtend(bitSize);
						op2 = factory.interval(w, w, bitSize); // w
						return op0.sar(op1.abstractGet()).or(op0.shl(op2.sub(op1.abstractGet()).abstractGet()).abstractGet());
				}
				assert false : "Unknown operator " + e.getOperator();
				return factory.top(bitSize);
			}

			@Override
			public AbstractDomain<T> visit(RTLSpecialExpression e) {
				assert !Options.failFast.getValue() : "Evaluated special expression";
				return factory.top(bitSize);
			}

			@Override
			public AbstractDomain<T> visit(RTLVariable e) {
				return s.getVariableValue(e).getLeft();
			}
		};
		AbstractDomain<T> result = e.accept(visitor);
		logger.verbose("evalExpression returned: " + result + " for " + e);
		return result;
	}

	@Override
	public String toString() {
		return s.toString();
	}
}
