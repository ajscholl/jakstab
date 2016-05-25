package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Pair;

import java.util.Collection;

public interface AbstractDomain<T extends Boxable<T>> extends AbstractState, AbstractValue, BitVectorType, Iterable<BitNumber> {

	/**
	 * Extract the T out of the abstract domain.
	 *
	 * @return The T.
	 */
	T abstractGet();

	@Override
	boolean hasUniqueConcretization();

	/**
	 * Get the unique value, if one exists.
	 *
	 * @return The unique value.
	 */
	BitNumber getUniqueConcretization();

	@Override
	AbstractDomain<T> join(LatticeElement l);

	/**
	 * Compute the greatest lower bound of two elements.
	 *
	 * @param t The other element.
	 * @return Their meet.
	 */
	AbstractDomain<T> meet(T t);

	@Override
	boolean lessOrEqual(LatticeElement l);

	@Override
	boolean isTop();

	@Override
	boolean isBot();

	/**
	 * Check if a value is in the abstract value.
	 *
	 * @param e The value.
	 * @return True if the value is in the abstract value.
	 */
	boolean hasElement(RTLNumber e);

	/**
	 * Check if a value is in the abstract value.
	 *
	 * @param e The value.
	 * @return True if the value is in the abstract value.
	 */
	boolean hasElement(BitNumber e);

	/**
	 * Compute the least upper bound of a set of abstract values.
	 *
	 * @param c A set of abstract values.
	 * @return The least upper bound.
	 */
	AbstractDomain<T> joins(Collection<T> c);

	/**
	 * Add two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> add(T t);

	/**
	 * Subtract two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> sub(T t);

	/**
	 * Negate the abstract value.
	 *
	 * @return The negated abstract value.
	 */
	AbstractDomain<T> negate();


	/**
	 * Multiply two abstract values and double the bit-width.
	 *
	 * @param t The other abstract value.
	 * @return The result, twice the bitsize.
	 */
	AbstractDomain<T> mulDouble(T t);

	/**
	 * Unsigned division of the abstract value by another abstract value. Division by 0 is assumed to return bot.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> unsignedDiv(T t);

	/**
	 * Signed division of the abstract value by another abstract value. Division by 0 is assumed to return bot as well as sMinBound / -1.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> signedDiv(T t);

	/**
	 * Unsigned remainder of two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The resulting abstract value.
	 */
	AbstractDomain<T> unsignedRem(T t);

	/**
	 * Signed remainder of two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The resulting abstract value.
	 */
	AbstractDomain<T> signedRem(T t);

	/**
	 * Compute the bitwise or of two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> or(T t);

	/**
	 * Compute the bitwise and of two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> and(T t);

	/**
	 * Compute the bitwise xor of two abstract values.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> xor(T t);

	/**
	 * Compute the bitwise not of an abstract value.
	 *
	 * @return The result.
	 */
	AbstractDomain<T> not();

	/**
	 * Cast the abstract value to the given bit-width, zero extending or truncating.
	 *
	 * @param bitSize The new bit-size.
	 * @return The result.
	 */
	AbstractDomain<T> cast(int bitSize);

	/**
	 * Sign extend from the specified first bit to the given last bit.
	 *
	 * @param firstBit First bit to extend from.
	 * @param lastBit Last bit to extend to. The result has at least this bitsize + 1 bits.
	 * @return The sign extended abstract value.
	 */
	AbstractDomain<T> signExtend(int firstBit, int lastBit);

	/**
	 * Sign extend an abstract value to the new bit width.
	 *
	 * @param bitSize The new bit width.
	 * @return The new abstract value.
	 */
	AbstractDomain<T> signExtend(int bitSize);

	/**
	 * Zero extend from the specified first bit to the given last bit.
	 *
	 * @param firstBit First bit to extend from.
	 * @param lastBit Last bit to extend to. The result has at least this bitsize + 1 bits.
	 * @return The zero extended abstract value.
	 */
	AbstractDomain<T> zeroExtend(int firstBit, int lastBit);

	/**
	 * Zero extend an abstract value to the new bit width.
	 *
	 * @param bitSize The new bit width.
	 * @return The new abstract value.
	 */
	AbstractDomain<T> zeroExtend(int bitSize);

	/**
	 * Truncate an abstract value to the given bit width.
	 *
	 * @param bitSize The new bit width.
	 * @return The new abstract value.
	 */
	AbstractDomain<T> truncate(int bitSize);

	/**
	 * Logical shift an abstract value to the left by another abstract value.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> shl(T t);

	/**
	 * Logical shift an abstract value to the right by another abstract value.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> shr(T t);

	/**
	 * Arithmetic shift an abstract value to the right by another abstract value.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> sar(T t);

	/**
	 * Equality.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> eq(T t);

	/**
	 * Signed less than.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> signedLessThan(T t);

	/**
	 * Signed less than or equal.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> signedLessThanOrEqual(T t);

	/**
	 * Unsigned less than.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> unsignedLessThan(T t);

	/**
	 * Unsigned less than or equal.
	 *
	 * @param t The other abstract value.
	 * @return The result.
	 */
	AbstractDomain<T> unsignedLessThanOrEqual(T t);

	/**
	 * Assume that this element is less or equal than another.
	 *
	 * @param t The greater or equal value.
	 * @return A pair containing the new abstract values for both operands.
	 */
	Pair<T, T> assumeULeq(T t);

	/**
	 * Assume that this element is less or equal than another.
	 *
	 * @param t The greater or equal value.
	 * @return A pair containing the new abstract values for both operands.
	 */
	Pair<T, T> assumeSLeq(T t);

	/**
	 * Widen one abstract value with another one.
	 *
	 * @param t The other abstract value.
	 * @return The widened abstract value.
	 */
	AbstractDomain<T> widen(T t);
}
