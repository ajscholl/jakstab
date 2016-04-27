package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Tuple;

import java.util.Collection;
import java.util.Set;

public interface AbstractDomainFactory<T extends AbstractValue & Boxable<T>> extends AbstractValueFactory<T> {
	AbstractDomain<T> number(long l, int bitSize);

	AbstractDomain<T> top(int bitSize);

	AbstractDomain<T> bot(int bitSize);

	AbstractDomain<T> number(RTLNumber e);

	AbstractDomain<T> interval(long w, long w1, int bitSize);

	T delegateJoins(int bitSize, Collection<T> l);

	Set<Tuple<RTLNumber>> delegateProjectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<T> evaluator);
}
