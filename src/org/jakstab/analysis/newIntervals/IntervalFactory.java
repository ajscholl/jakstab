package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Lattices;
import org.jakstab.util.Logger;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public final class IntervalFactory implements AbstractValueFactory<Interval> {

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalFactory.class);

	private static final IntervalFactory factory = new IntervalFactory();

	private IntervalFactory() {
	}

	@Override
	public Interval createAbstractValue(RTLNumber n) {
		return new Interval(n);
	}

	@Override
	public Interval createAbstractValue(Collection<RTLNumber> numbers) {
		List<Interval> abstractValues = new ArrayList<>();
		for (RTLNumber n : numbers) {
			abstractValues.add(createAbstractValue(n));
		}
		return Lattices.joinAll(abstractValues);
	}

	@Override
	public Interval createTop(int bitWidth) {
		return Interval.mkTopInterval(Bits.fromInt(bitWidth));
	}

	@Override
	public Interval createFalse() {
		return new Interval(ExpressionFactory.createNumber(0L, 1));
	}

	@Override
	public Interval createTrue() {
		return new Interval(ExpressionFactory.createNumber(1L, 1));
	}

	public static IntervalFactory getFactory() {
		return factory;
	}
}

