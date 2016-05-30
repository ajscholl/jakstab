package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
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
 * Factory for cc-intervals.
 *
 * @author A. J. Scholl
 */
final class CongruenceClassIntervalFactory implements AbstractDomainFactory<CongruenceClassInterval> {

	/**
	 * Logger.
	 */
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(CongruenceClassIntervalFactory.class);

	/**
	 * Shared factory object.
	 */
	private static final CongruenceClassIntervalFactory factory = new CongruenceClassIntervalFactory();

	/**
	 * Empty constructor.
	 */
	private CongruenceClassIntervalFactory() {
	}

	/**
	 * Retrieve the factory.
	 *
	 * @return The factory.
	 */
	public static CongruenceClassIntervalFactory getFactory() {
		return factory;
	}

	@Override
	public CongruenceClassInterval number(long n, int bitSize) {
		return CongruenceClassInterval.number(BitNumber.valueOf(n, bitSize));
	}

	@Override
	public CongruenceClassInterval top(int bitSize) {
		return CongruenceClassInterval.top(bitSize);
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> bot(int bitSize) {
		return CongruenceClassInterval.bot(bitSize);
	}

	@Override
	public CongruenceClassInterval number(RTLNumber n) {
		return CongruenceClassInterval.number(BitNumber.valueOf(n));
	}

	@Override
	public CongruenceClassInterval interval(long a, long b, int bitSize) {
		return CongruenceClassInterval.ccInterval(BitNumber.valueOf(a, bitSize), BitNumber.valueOf(b, bitSize));
	}

	@Override
	public CongruenceClassInterval delegateJoins(int bitSize, Collection<CongruenceClassInterval> l) {
		return CongruenceClassInterval.joinsCC(bitSize, l);
	}

	@Override
	public Set<Tuple<RTLNumber>> delegateProjectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<CongruenceClassInterval> evaluator) {
		return CongruenceClassInterval.projectionFromConcretization(expressions, evaluator);
	}

	@Override
	public CongruenceClassInterval createAbstractValue(RTLNumber n) {
		return CongruenceClassInterval.number(BitNumber.valueOf(n));
	}

	@Override
	public CongruenceClassInterval createAbstractValue(Collection<RTLNumber> numbers) {
		int bitSize = -1;
		List<CongruenceClassInterval> xs = new ArrayList<>(numbers.size());
		for (RTLNumber x : numbers) {
			assert bitSize == -1 || x.getBitWidth() == bitSize;
			xs.add(createAbstractValue(x));
			bitSize = x.getBitWidth();
		}
		assert bitSize != -1;
		return CongruenceClassInterval.joinsCC(bitSize, xs);
	}

	@Override
	public CongruenceClassInterval createTop(int bitWidth) {
		return top(bitWidth);
	}

	@Override
	public CongruenceClassInterval createTrue() {
		return CongruenceClassInterval.TRUE_CC_INTERVAL;
	}

	@Override
	public CongruenceClassInterval createFalse() {
		return CongruenceClassInterval.FALSE_CC_INTERVAL;
	}
}

