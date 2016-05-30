package org.jakstab.analysis.signagnostic;

import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;

import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.TreeMap;

/**
 * Value valuation specialized to memory regions. Code copied and adapted from {@link org.jakstab.analysis.VariableValuation},
 * originally written by Johannes Kinder.
 *
 * @author A. J. Scholl
 */
class VariableRegion implements LatticeElement, Iterable<Entry<RTLVariable, MemoryRegion>> {

	/**
	 * Logger.
	 */
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(VariableRegion.class);

	private final Map<RTLVariable, MemoryRegion> regions;

	private VariableRegion(Map<RTLVariable, MemoryRegion> regions) {
		assert regions != null;
		this.regions = regions;
	}

	VariableRegion(VariableRegion proto) {
		this(new TreeMap<>(proto.regions));
	}

	VariableRegion() {
		this(new TreeMap<RTLVariable, MemoryRegion>());
	}

	public MemoryRegion get(RTLVariable var) {
		MemoryRegion e = regions.get(var);
		if (e != null) {
			return e;
		} else {
			return MemoryRegion.TOP;
		}
	}

	private void clearCovering(RTLVariable var) {
		for (RTLVariable covering : ExpressionFactory.coveringRegisters(var)) {
			regions.remove(covering);
			//clearCovering(covering);
		}
	}

	private void clearCovered(RTLVariable var) {
		for (RTLVariable covered : ExpressionFactory.coveredRegisters(var)) {
			regions.remove(covered);
			//clearCovered(covered);
		}
	}

	public void set(RTLVariable var, MemoryRegion region) {
		clearCovering(var);
		clearCovered(var);
		if (region.isTop()) {
			regions.remove(var);
		} else {
			regions.put(var, region);
		}
	}

	public void setTop(RTLVariable var) {
		clearCovering(var);
		clearCovered(var);
		regions.remove(var);
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return regions.isEmpty();
	}

	@Override
	public VariableRegion join(LatticeElement l) {
		VariableRegion other = (VariableRegion) l;
		if (isTop() || other.isBot()) {
			return this;
		}
		if (isBot() || other.isTop()) {
			return other;
		}
		VariableRegion joinedValuation = new VariableRegion();
		for (Entry<RTLVariable, MemoryRegion> entry : regions.entrySet()) {
			RTLVariable var = entry.getKey();
			joinedValuation.set(var, entry.getValue().join(other.get(var)));
		}
		return joinedValuation;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		VariableRegion other = (VariableRegion) l;
		if (other.isTop()) {
			return true;
		}
		if (isTop()) {
			return false;
		}
		// For all variables in other regions, check if their
		// region in this regions is less. Other way round is not
		// possible, as their could be variables present in the other
		// valuation but not in this one.
		for (Entry<RTLVariable,MemoryRegion> entry : other.regions.entrySet()) {
			RTLVariable var = entry.getKey();
			MemoryRegion value = entry.getValue();
			if (!get(var).lessOrEqual(value)) {
				return false;
			}
		}
		return true;
	}

	@Override
	public String toString() {
		return regions.toString();
	}

	@Override
	public int hashCode() {
		return regions.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null) {
			return false;
		}
		if (getClass() != obj.getClass()) {
			return false;
		}
		VariableRegion other = (VariableRegion) obj;
		return regions.equals(other.regions);
	}

	@Override
	public Iterator<Entry<RTLVariable, MemoryRegion>> iterator() {
		return regions.entrySet().iterator();
	}

}
