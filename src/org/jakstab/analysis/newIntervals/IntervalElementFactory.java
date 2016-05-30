package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.newIntervals.abstracted.AbstractDomainFactory;
import org.jakstab.analysis.newIntervals.abstracted.AbstractEvaluator;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Logger;
import org.jakstab.util.Tuple;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

/**
 * Factory for intervals.
 *
 * @author A. J. Scholl
 */
final class IntervalElementFactory implements AbstractDomainFactory<IntervalElement> {

	/**
	 * Logger.
	 */
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalElementFactory.class);

	/**
	 * Shared factory object.
	 */
	private static final IntervalElementFactory factory = new IntervalElementFactory();

	/**
	 * Empty constructor.
	 */
	private IntervalElementFactory() {
	}

	/**
	 * Retrieve the factory.
	 *
	 * @return The factory.
	 */
	public static IntervalElementFactory getFactory() {
		return factory;
	}

	@Override
	public IntervalElement number(long n, int bitSize) {
		return IntervalElement.number(n, bitSize);
	}

	@Override
	public IntervalElement top(int bitSize) {
		return IntervalElement.top(bitSize);
	}

	@Override
	public IntervalElement bot(int bitSize) {
		return IntervalElement.bot(bitSize);
	}

	@Override
	public IntervalElement number(RTLNumber n) {
		return IntervalElement.number(n);
	}

	@Override
	public IntervalElement interval(long a, long b, int bitSize) {
		return IntervalElement.interval(BitNumber.valueOf(a, bitSize), BitNumber.valueOf(b, bitSize));
	}

	@Override
	public IntervalElement delegateJoins(int bitSize, Collection<IntervalElement> l) {
		return IntervalElement.joins(bitSize, l);
	}

	@Override
	public Set<Tuple<RTLNumber>> delegateProjectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<IntervalElement> evaluator) {
		return IntervalElement.projectionFromConcretization(expressions, evaluator);
	}

	@Override
	public IntervalElement createAbstractValue(RTLNumber n) {
		return IntervalElement.number(n);
	}

	@Override
	public IntervalElement createAbstractValue(Collection<RTLNumber> numbers) {
		int bitSize = -1;
		List<IntervalElement> xs = new ArrayList<>(numbers.size());
		for (RTLNumber x : numbers) {
			assert bitSize == -1 || x.getBitWidth() == bitSize;
			xs.add(createAbstractValue(x));
			bitSize = x.getBitWidth();
		}
		assert bitSize != -1;
		return IntervalElement.joins(bitSize, xs);
	}

	@Override
	public IntervalElement createTop(int bitWidth) {
		return top(bitWidth);
	}

	@Override
	public IntervalElement createTrue() {
		return IntervalElement.TRUE_INTERVAL;
	}

	@Override
	public IntervalElement createFalse() {
		return IntervalElement.FALSE_INTERVAL;
	}
}

