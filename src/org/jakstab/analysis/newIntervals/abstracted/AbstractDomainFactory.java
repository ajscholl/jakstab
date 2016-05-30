package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Tuple;

import java.util.Collection;
import java.util.Set;

/**
 * Interface for factories for abstract domains.
 *
 * @author A. J. Scholl
 * @param <T> Thing the factory can produce.
 */
public interface AbstractDomainFactory<T extends AbstractValue & Boxable<T>> extends AbstractValueFactory<T> {

	/**
	 * Create a number with the given value and size.
	 *
	 * @param l The value.
	 * @param bitSize The size.
	 * @return The number.
	 */
	AbstractDomain<T> number(long l, int bitSize);

	/**
	 * Create a number from an {@link RTLNumber}.
	 *
	 * @param e The value.
	 * @return The number.
	 */
	AbstractDomain<T> number(RTLNumber e);

	/**
	 * Create top.
	 *
	 * @param bitSize The number of bits in top.
	 * @return Top.
	 */
	AbstractDomain<T> top(int bitSize);

	/**
	 * Create bot.
	 *
	 * @param bitSize The number of bits in bot.
	 * @return Bot.
	 */
	AbstractDomain<T> bot(int bitSize);

	/**
	 * Create an interval from start to end.
	 *
	 * @param start Start of the interval.
	 * @param end End of the interval.
	 * @param bitSize The number of bits.
	 * @return An interval from start to end.
	 */
	AbstractDomain<T> interval(long start, long end, int bitSize);

	/**
	 * Set-join operator, joins every element in the collection. Every element should have the given bitsize, which is
	 * used if the collection is empty.
	 *
	 * @param bitSize The number of bits of every element.
	 * @param l The elements to join.
	 * @return An upper bound for all elements.
	 */
	T delegateJoins(int bitSize, Collection<T> l);

	/**
	 * Perform a projection from concretization for the given expressions. Used to pass an additional evaluator.
	 *
	 * @param expressions The array of expressions to project.
	 * @param evaluator An evaluator to compute their valuation.
	 * @return A projection.
	 */
	Set<Tuple<RTLNumber>> delegateProjectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<T> evaluator);
}
