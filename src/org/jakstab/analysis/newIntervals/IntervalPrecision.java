package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.Precision;
import org.jakstab.util.Logger;

public class IntervalPrecision implements Precision {

	private static final Logger logger = Logger.getLogger(IntervalPrecision.class);

	private final int count;

	public IntervalPrecision() {
		this(0);
	}

	private IntervalPrecision(int c) {
		count = c;
	}

	public IntervalPrecision inc() {
		logger.debug("Incrementing precision to " + (count + 1));
		return new IntervalPrecision(count + 1);
	}

	public int getCount() {
		return count;
	}

	@Override
	public String toString() {
		return "Count: " + count;
	}
}
