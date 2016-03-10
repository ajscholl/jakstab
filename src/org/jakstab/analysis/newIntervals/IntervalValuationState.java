package org.jakstab.analysis.newIntervals;

import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap.EntryIterator;
import org.jakstab.util.Pair;
import org.jakstab.util.Tuple;

import java.math.BigInteger;
import java.util.Iterator;
import java.util.Map.Entry;
import java.util.Set;

public class IntervalValuationState implements AbstractState {

	private static final Logger logger = Logger.getLogger(IntervalValuationState.class);

	private static long maxStateId = 0L;

	private final long id;
	private final VariableValuation<Interval> varVal;
	private final PartitionedMemory<Interval> store;
	private final VariableRegion varRegions;

	public IntervalValuationState(IntervalValuationState proto) {
		this(new VariableValuation<>(proto.varVal), new PartitionedMemory<>(proto.store), new VariableRegion(proto.varRegions));
	}

	public IntervalValuationState() {
		this(new VariableValuation<>(IntervalFactory.getFactory()), new PartitionedMemory<>(IntervalFactory.getFactory()), new VariableRegion());
	}

	private IntervalValuationState(VariableValuation<Interval> varVal, PartitionedMemory<Interval> store, VariableRegion varRegions) {
		assert varVal != null;
		assert store != null;
		this.varVal = varVal;
		this.store = store;
		this.varRegions = varRegions;
		id = maxStateId;
		incId();
	}

	private static void incId() {
		maxStateId++;
	}

	public Interval abstractEval(RTLExpression e) {
		return Interval.abstractEval(e, this);
	}

	public void setMemoryValue(RTLMemoryLocation location, Interval value) {
		Interval address = Interval.abstractEval(location.getAddress(), this);
		setMemoryValue(address, value);
	}

	public void setMemoryValue(Interval address, Interval value) {
		int bitWidth = value.getBitWidth();
		if (address.hasUniqueConcretization()) {
			setMemoryValue(MemoryRegion.GLOBAL, address.getUniqueConcretization(), bitWidth, value);
		}
		if (address.isTop() || address.size().compareTo(BigInteger.valueOf(0xFFL)) > 0) {
			if (!store.isTop()) {
				assert !Options.failFast.getValue() : "Overwritten too much memory (" + address + ") when writing " + address + " with value " + value + " with memory " + store;
				for (EntryIterator<MemoryRegion, Long, Interval> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
					store.set(entryIt.getLeftKey(), entryIt.getRightKey(), value.getBitWidth(), entryIt.getValue().join(value));
				}
			}
			return;
		}
		assert !address.isBot() : "Written BOT memory location";
		assert address.size().compareTo(BigInteger.valueOf(0xFFL)) <= 0 : "Iterating over large interval";
		for (Long offset : address) {
			Interval oldVal = getMemoryValue(MemoryRegion.GLOBAL, offset, bitWidth);
			setMemoryValue(MemoryRegion.GLOBAL, offset, bitWidth, value.join(oldVal));
		}
	}

	public void setMemoryValue(MemoryRegion region, long offset, int bitWidth, Interval value) {
		assert region.equals(MemoryRegion.TOP) : "PartitionedMemory does not like TOP";
		store.set(region, offset, bitWidth, value);
	}

	public void setVariableValue(RTLVariable var, Interval value, MemoryRegion region) {
		logger.debug("Setting " + var + " to " + value + '/' + region + " in state " + id);
		varVal.set(var, value);
		varRegions.set(var, region);
	}

	public Interval getMemoryValue(Interval address, int bitWidth) {
		if (address.isTop() || address.size().compareTo(BigInteger.valueOf(0xFFL)) > 0) {
			return Interval.mkTopInterval(Bits.fromInt(bitWidth));
		}
		if (address.isBot()) {
			return Interval.mkBotInterval(Bits.fromInt(bitWidth));
		}
		Set<Interval> results = new FastSet<>();
		for (Long offset : address) {
			results.add(getMemoryValue(MemoryRegion.GLOBAL, offset, bitWidth));
		}
		return Interval.joins(results);
	}

	public Interval getMemoryValue(RTLMemoryLocation e) {
		Interval iAddress = Interval.abstractEval(e.getAddress(), this);
		return getMemoryValue(iAddress, e.getBitWidth());
	}

	public Interval getMemoryValue(MemoryRegion region, long offset, int bitWidth) {
		return store.get(region, offset, bitWidth);
	}

	public Pair<Interval, MemoryRegion> getVariableValue(RTLVariable var) {
		return new Pair<>(varVal.get(var), varRegions.get(var));
	}

	public Iterator<Entry<RTLVariable, Interval>> variableIterator() {
		return varVal.iterator();
	}

	public EntryIterator<MemoryRegion, Long, Interval> storeIterator() {
		return store.entryIterator();
	}

	@Override
	public String getIdentifier() {
		return toString();
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public IntervalValuationState join(LatticeElement l) {
		IntervalValuationState other = (IntervalValuationState) l;
		if (isTop() || other.isBot()) {
			return this;
		}
		if (isBot() || other.isTop()) {
			return other;
		}
		return new IntervalValuationState(varVal.join(other.varVal), store.join(other.store), varRegions.join(other.varRegions));
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return Interval.projectionFromConcretization(expressions, this);
	}

	@Override
	public boolean isBot() {
		return false;
	}

	@Override
	public boolean isTop() {
		return varVal.isTop() && store.isTop() && varRegions.isTop();
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if (isBot() || l.isTop()) {
			return true;
		}
		if (isTop() || l.isBot()) {
			return false;
		}
		IntervalValuationState other = (IntervalValuationState) l;
		return varVal.lessOrEqual(other.varVal) && store.lessOrEqual(other.store) && varRegions.lessOrEqual(other.varRegions);

	}

	@Override
	public String toString() {
		return "[" + id + "] I: " + varVal + " Mem:" + store + " Regions: " + varRegions;
	}

	@Override
	public int hashCode() {
		return store.hashCode() ^ varVal.hashCode() ^ varRegions.hashCode();
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		IntervalValuationState other = (IntervalValuationState) obj;
		return store.equals(other.store) && varVal.equals(other.varVal) && varRegions.equals(other.varRegions);
	}
}
