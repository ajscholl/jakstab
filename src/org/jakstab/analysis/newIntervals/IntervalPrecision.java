package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.Precision;
import org.jakstab.util.Logger;

/**
 * Precision for intervals and cc-intervals counts up. If a fixed value is reached, {@link GenericValuationState} performs widening.
 *
 * @author A. J. Scholl
 */
class IntervalPrecision implements Precision {

	/**
	 * Logger.
	 */
	private static final Logger logger = Logger.getLogger(IntervalPrecision.class);

	/**
	 * Current count, immutable.
	 */
	private final int count;

	/**
	 * Create a new precision.
	 */
	IntervalPrecision() {
		this(0);
	}

	/**
	 * Create a new precision with the given value.
	 *
	 * @param c The value.
	 */
	private IntervalPrecision(int c) {
		count = c;
	}

	/**
	 * Increment the precision to the next value.
	 *
	 * @return A new precision.
	 */
	public IntervalPrecision inc() {
		logger.debug("Incrementing precision to " + (count + 1));
		return new IntervalPrecision(count + 1);
	}

	/**
	 * Retrieve the current count.
	 *
	 * @return The current count (number of iterations).
	 */
	public int getCount() {
		return count;
	}

	@Override
	public String toString() {
		return "Count: " + count;
	}
}
