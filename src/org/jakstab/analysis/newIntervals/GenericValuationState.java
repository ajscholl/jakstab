package org.jakstab.analysis.newIntervals;

import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.analysis.newIntervals.abstracted.*;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap.EntryIterator;
import org.jakstab.util.Pair;
import org.jakstab.util.Tuple;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map.Entry;
import java.util.Set;

final class GenericValuationState<T extends AbstractDomain<T> & Boxable<T>> implements AbstractState, AbstractValuationState<T> {

	private static final Logger logger = Logger.getLogger(GenericValuationState.class);

	private static long maxStateId = 0L;

	private final long id;
	private final VariableValuation<T> varVal;
	private final PartitionedMemory<T> store;
	private final AbstractDomainFactory<T> factory;
	private final AbstractEvaluator<T> eval;
	private final VariableRegion varRegions;

	public GenericValuationState(GenericValuationState<T> proto) {
		this(new VariableValuation<>(proto.varVal), new PartitionedMemory<>(proto.store), proto.factory, new VariableRegion(proto.varRegions));
	}

	public GenericValuationState(AbstractDomainFactory<T> factory) {
		this(new VariableValuation<>(factory), new PartitionedMemory<>(factory), factory, new VariableRegion());
	}

	private GenericValuationState(VariableValuation<T> varVal,
								  PartitionedMemory<T> store,
								  AbstractDomainFactory<T> factory,
								  VariableRegion varRegions) {
		assert varVal != null;
		assert store != null;
		this.varVal = varVal;
		this.store = store;
		this.factory = factory;
		this.varRegions = varRegions;
		eval = new AbstractEvaluator<>(factory, this);
		id = maxStateId;
		incId();
	}

	private static void incId() {
		maxStateId++;
	}

	public T abstractEval(RTLExpression e) {
		return eval.evalExpression(e).abstractGet();
	}

	public void setMemoryValue(RTLMemoryLocation location, T value) {
		T address = eval.evalExpression(location.getAddress()).abstractGet();
		setMemoryValue(address, value);
	}

	public void setMemoryValue(T address, T value) {
		int bitWidth = value.getBitWidth();
		if (address.hasUniqueConcretization()) {
			setMemoryValue(MemoryRegion.GLOBAL, address.getUniqueConcretization().zExtLongValue(), bitWidth, value);
		}
		if (address.isTop()) {
			if (!store.isTop()) {
				assert !Options.failFast.getValue() : "Overwritten too much memory (" + address + ") when writing " + address + " with value " + value + " with memory " + store;
				for (EntryIterator<MemoryRegion, Long, T> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
					store.set(entryIt.getLeftKey(), entryIt.getRightKey(), value.getBitWidth(), entryIt.getValue().join(value).abstractGet());
				}
			}
			return;
		}
		for (BitNumber offset : address) {
			AbstractValue oldVal = getMemoryValue(MemoryRegion.GLOBAL, offset.zExtLongValue(), bitWidth);
			setMemoryValue(MemoryRegion.GLOBAL, offset.zExtLongValue(), bitWidth, value.join(oldVal).abstractGet());
		}
	}

	public void setMemoryValue(MemoryRegion region, long offset, int bitWidth, T value) {
		assert region.equals(MemoryRegion.TOP) : "PartitionedMemory does not like TOP";
		store.set(region, offset, bitWidth, value);
	}

	public void setVariableValue(RTLVariable var, T value, MemoryRegion region) {
		logger.debug("Setting " + var + " to " + value + '/' + region + " in state " + id);
		varVal.set(var, value);
		varRegions.set(var, region);
	}

	public T getMemoryValue(T address, int bitWidth) {
		if (address.isTop()) {
			return factory.top(bitWidth).abstractGet();
		}
		if (address.isBot()) {
			return factory.bot(bitWidth).abstractGet();
		}
		List<T> results = new ArrayList<>();
		for (BitNumber offset : address) {
			results.add(getMemoryValue(MemoryRegion.GLOBAL, offset.zExtLongValue(), bitWidth));
		}
		return factory.delegateJoins(bitWidth, results);
	}

	public AbstractDomain<T> getMemoryValue(RTLMemoryLocation e) {
		T iAddress = eval.evalExpression(e.getAddress()).abstractGet();
		return getMemoryValue(iAddress, e.getBitWidth());
	}

	public T getMemoryValue(MemoryRegion region, long offset, int bitWidth) {
		return store.get(region, offset, bitWidth);
	}

	public Pair<AbstractDomain<T>, MemoryRegion> getVariableValue(RTLVariable var) {
		return new Pair<>(varVal.get(var).abstractBox(), varRegions.get(var));
	}

	public Iterator<Entry<RTLVariable, T>> variableIterator() {
		return varVal.iterator();
	}

	public EntryIterator<MemoryRegion, Long, T> storeIterator() {
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
	@SuppressWarnings("unchecked")
	public GenericValuationState<T> join(LatticeElement l) {
		GenericValuationState<T> other = (GenericValuationState<T>) l;
		if (isTop() || other.isBot()) {
			return this;
		}
		if (isBot() || other.isTop()) {
			return other;
		}
		return new GenericValuationState<>(varVal.join(other.varVal), store.join(other.store), factory, varRegions.join(other.varRegions));
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return factory.delegateProjectionFromConcretization(expressions, eval);
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
	@SuppressWarnings("unchecked")
	public boolean lessOrEqual(LatticeElement l) {
		if (isBot() || l.isTop()) {
			return true;
		}
		if (isTop() || l.isBot()) {
			return false;
		}
		GenericValuationState<T> other = (GenericValuationState<T>) l;
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
	@SuppressWarnings("unchecked")
	public boolean equals(Object obj) {
		if (this == obj) {
			return true;
		}
		if (obj == null || getClass() != obj.getClass()) {
			return false;
		}
		GenericValuationState<T> other = (GenericValuationState<T>) obj;
		return store.equals(other.store) && varVal.equals(other.varVal) && varRegions.equals(other.varRegions);
	}
}
