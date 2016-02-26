package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.Precision;

public class IntervalPrecision implements Precision {
	private final int count;

	public IntervalPrecision() {
		count = 0;
	}

	private IntervalPrecision(int c) {
		count = c;
	}

	public IntervalPrecision copy() {
		return new IntervalPrecision(count);
	}

	public IntervalPrecision inc() {
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
