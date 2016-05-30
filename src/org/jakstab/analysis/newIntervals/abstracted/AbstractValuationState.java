package org.jakstab.analysis.newIntervals.abstracted;

import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Pair;

/**
 * Interface for states storing memory and variable values.
 *
 * @author A. J. Scholl
 * @param <T> The thing stored in the state.
 */
public interface AbstractValuationState<T extends Boxable<T>> {
	AbstractDomain<T> getMemoryValue(RTLMemoryLocation m);

	Pair<AbstractDomain<T>, MemoryRegion> getVariableValue(RTLVariable e);
}
