package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Pair;

public interface AbstractValuationState<T extends Boxable<T>> {
	AbstractDomain<T> getMemoryValue(RTLMemoryLocation m);

	Pair<AbstractDomain<T>, MemoryRegion> getVariableValue(RTLVariable e);
}
