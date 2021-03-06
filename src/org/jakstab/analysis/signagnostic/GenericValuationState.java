package org.jakstab.analysis.signagnostic;

import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.analysis.signagnostic.abstracted.*;
import org.jakstab.analysis.signagnostic.utils.BitNumber;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

import java.util.*;
import java.util.Map.Entry;

/**
 * Valuation state for interval analyses. Could work for other analyses, too.
 *
 * @param <T> The type of the interval.
 */
final class GenericValuationState<T extends AbstractDomain<T> & Boxable<T>> implements AbstractState, AbstractValuationState<T> {

	/**
	 * Logger.
	 */
	private static final Logger logger = Logger.getLogger(GenericValuationState.class);

	/**
	 * Id of the next state.
	 */
	private static long maxStateId = 0L;

	/**
	 * Id of this state.
	 */
	final long id;

	/**
	 * Variables of this state.
	 */
	private final VariableValuation<T> varVal;

	/**
	 * Memory of this state.
	 */
	final PartitionedMemory<T> store;

	/**
	 * Variable regions for this state.
	 */
	private final VariableRegion varRegions;

	/**
	 * Factory for elements for this state.
	 */
	private final AbstractDomainFactory<T> factory;

	/**
	 * Evaluator to use with this state.
	 */
	private final AbstractEvaluator<T> eval;

	/**
	 * Counter for allocations for this state.
	 */
	private final AllocationCounter allocationCounter;

	/**
	 * If set to true, widen instead of joining.
	 */
	private boolean widen;

	/**
	 * Copy constructor.
	 *
	 * @param proto State to copy.
	 */
	GenericValuationState(GenericValuationState<T> proto) {
		this(new VariableValuation<>(proto.varVal),
			 new PartitionedMemory<>(proto.store),
			 proto.factory,
			 new VariableRegion(proto.varRegions),
			 AllocationCounter.create(proto.allocationCounter),
			 proto.widen);
	}

	/**
	 * Create a new state.
	 *
	 * @param factory Factory for elements of the state.
	 */
	GenericValuationState(AbstractDomainFactory<T> factory) {
		this(new VariableValuation<>(factory), new PartitionedMemory<>(factory), factory, new VariableRegion(), new AllocationCounter(), false);
	}

	/**
	 * Create a new state.
	 *
	 * @param varVal Variable valuation for the new state.
	 * @param store Memory valuation for the new state.
	 * @param factory Factory for the new state.
	 * @param varRegions Regions for the new state.
	 * @param allocationCounter Allocation information for the new state.
	 * @param widen Widen flag for the new state.
	 */
	private GenericValuationState(VariableValuation<T> varVal,
								  PartitionedMemory<T> store,
								  AbstractDomainFactory<T> factory,
								  VariableRegion varRegions,
								  AllocationCounter allocationCounter,
								  boolean widen) {
		assert varVal != null;
		assert store != null;
		id = maxStateId;
		incId();
		this.varVal = varVal;
		this.store = store;
		this.factory = factory;
		this.varRegions = varRegions;
		this.allocationCounter = allocationCounter;
		this.widen = widen;
		eval = new AbstractEvaluator<>(factory, this);
	}

	/**
	 * Advance the id for the next state.
	 */
	private static void incId() {
		maxStateId++;
	}

	/**
	 * Set widen to true, thus widening instead of joining.
	 */
	private void activateWiden() {
		widen = true;
	}

	/**
	 * Evaluate an expression in this state.
	 *
	 * @param e The expression.
	 * @return The value of the expression.
	 */
	public T abstractEval(RTLExpression e) {
		return eval.evalExpression(e).abstractGet();
	}

	/**
	 * Get the region of an expression.
	 *
	 * @param location The expression we want the region of.
	 * @return The region of the expression.
	 */
	public MemoryRegion getRegion(RTLExpression location) {
		logger.debug("Computing region for " + location);
		MemoryRegion region = null;
		for (RTLVariable v : location.getUsedVariables()) {
			MemoryRegion r = getVariableValue(v).getRight();
			logger.debug("  Found variable " + v + " with region " + r);
			region = region == null ? r : region.join(r);
		}
		logger.debug("Computed region " + region);
		return region == null ? MemoryRegion.GLOBAL : region;
	}

	/**
	 * Set the value of a memory location to a value.
	 *
	 * @param location The location.
	 * @param value The new value of the location.
	 */
	void setMemoryValue(RTLMemoryLocation location, T value) {
		logger.debug("Setting memory location " + location + " to " + value);
		T address = eval.evalExpression(location.getAddress()).abstractGet();
		MemoryRegion region = getRegion(location);
		logger.debug("Evaluated address to " + address + " in region " + region);
		if (region.equals(MemoryRegion.TOP)) {
			store.setTop(region);
		} else {
			setMemoryValue(address, value, region);
		}
	}

	/**
	 * Set the memory address of a memory region given by some domain value.
	 *
	 * @param address The address.
	 * @param value The new value.
	 * @param region The region of the address. Should not be TOP.
	 */
	void setMemoryValue(T address, T value, MemoryRegion region) {
		assert !region.equals(MemoryRegion.TOP);
		int bitWidth = value.getBitWidth();
		if (address.hasUniqueConcretization()) {
			setMemoryValue(region, address.getUniqueConcretization().zExtLongValue(), bitWidth, value);
		} else if (address.isTop()) {
			if (!store.isTop()) {
				assert !Options.failFast.getValue() : "Overwritten too much memory (" + address + ") when writing " + address + " with value " + value + " with memory " + store;
				for (EntryIterator<MemoryRegion, Long, T> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
					T val = entryIt.getValue();
					int valueBits = value.getBitWidth();
					if (val.getBitWidth() < valueBits) {
						// just assume these bits are set to 0
						// this may not be always correct, but we can not handle it here as we do not know the endianness
						// of the memory. also, if we have to jam the upper bits of an interval, we most likely will get
						// TOP, so... yeah.
						val = val.zeroExtend(valueBits).abstractGet();
						// lets just fail for the moment and see how often this happens
						assert false : "Unsound zero extension of " + entryIt.getValue() + " to " + val;
					} else if (val.getBitWidth() > value.getBitWidth()) {
						val = val.truncate(value.getBitWidth()).abstractGet();
					}
					store.set(entryIt.getLeftKey(), entryIt.getRightKey(), value.getBitWidth(), val.join(value).abstractGet());
				}
			}
		} else {
			logger.verbose("Setting multiple memory locations. Setting " + address + " to " + value + " in region " + region);
			int i = 0;
			for (BitNumber offset : address) {
				i++;
				if (i < 100) {
					AbstractValue oldVal = getMemoryValue(region, offset.zExtLongValue(), bitWidth);
					store.weakUpdate(region, offset.zExtLongValue(), bitWidth, value);
					AbstractValue newVal = getMemoryValue(region, offset.zExtLongValue(), bitWidth);
					logger.verbose("Read " + offset + " with " + oldVal + ", Written " + newVal);
				} else {
					store.setTop(region);
					break;
				}
			}
		}
	}

	/**
	 * Set the memory value at the given offset in some region.
	 *
	 * @param region The region.
	 * @param offset The offset in the region.
	 * @param bitWidth The width in bits.
	 * @param value The new memory value.
	 */
	private void setMemoryValue(MemoryRegion region, long offset, int bitWidth, T value) {
		if (region.equals(MemoryRegion.TOP)) {
			store.setTop(region);
		} else {
			store.set(region, offset, bitWidth, value);
		}
	}

	/**
	 * Set the value of a variable.
	 *
	 * @param var The variable.
	 * @param value The new value of the variable.
	 * @param region The new region of the variable.
	 */
	void setVariableValue(RTLVariable var, T value, MemoryRegion region) {
		logger.debug("Setting " + var + " to " + value + '/' + region + " in state " + id);
		varVal.set(var, value);
		varRegions.set(var, region);
	}

	/**
	 * Retrieve a value stored in memory.
	 *
	 * @param address The memory address.
	 * @return The value stored there.
	 */
	public T getMemoryValue(RTLMemoryLocation address) {
		logger.debug("Getting memory value at " + address);
		T addressValue = eval.evalExpression(address.getAddress()).abstractGet();
		MemoryRegion region = getRegion(address);
		logger.debug("Address evaluated to " + addressValue + " in region " + region);
		return getMemoryValue(addressValue, region, address.getBitWidth());
	}

	/**
	 * Retrieve a value stored somewhere in some region.
	 *
	 * @param address The address of the value.
	 * @param region The region of the value.
	 * @param bitWidth The width in bits.
	 * @return An approximation of the value.
	 */
	private T getMemoryValue(T address, MemoryRegion region, int bitWidth) {
		if (address.isTop()) {
			return factory.top(bitWidth).abstractGet();
		}
		if (address.isBot()) {
			return factory.bot(bitWidth).abstractGet();
		}
		List<T> results = new ArrayList<>();
		int i = 0;
		for (BitNumber offset : address) {
			i++;
			if (i > 100) {
				return factory.createTop(bitWidth);
			}
			results.add(getMemoryValue(region, offset.zExtLongValue(), bitWidth));
		}
		return factory.delegateJoins(bitWidth, results);
	}

	/**
	 * Retrieve a value in memory.
	 *
	 * @param region The region.
	 * @param offset The offset in the region.
	 * @param bitWidth The width in bits.
	 * @return The value stored there.
	 */
	private T getMemoryValue(MemoryRegion region, long offset, int bitWidth) {
		if (region.equals(MemoryRegion.TOP)) {
			return factory.createTop(bitWidth);
		}
		return store.get(region, offset, bitWidth);
	}

	/**
	 * Get the value and region of a variable.
	 *
	 * @param var The variable.
	 * @return Value and region.
	 */
	public Pair<AbstractDomain<T>, MemoryRegion> getVariableValue(RTLVariable var) {
		return new Pair<>(varVal.get(var).abstractBox(), varRegions.get(var));
	}

	/**
	 * Get an iterator for all variables.
	 *
	 * @return The iterator.
	 */
	private Iterator<Entry<RTLVariable, T>> variableIterator() {
		return varVal.iterator();
	}

	/**
	 * Get an iterator over the memory.
	 *
	 * @return The iterator.
	 */
	private EntryIterator<MemoryRegion, Long, T> storeIterator() {
		return store.entryIterator();
	}

	/**
	 * Widen a state with another state.
	 *
	 * @param other The other state.
	 * @return Some state larger than both inputs.
	 */
	GenericValuationState<T> widen(GenericValuationState<T> other) {
		GenericValuationState<T> widenedState = new GenericValuationState<>(factory);
		widenedState.activateWiden();
		// Widen variable valuations
		for (Entry<RTLVariable,T> entry : new IterableIterator<>(variableIterator())) {
			RTLVariable var = entry.getKey();
			T v = entry.getValue();
			Pair<AbstractDomain<T>, MemoryRegion> vv = other.getVariableValue(var);
			T u = vv.getLeft().abstractGet();
			T r = v.widen(u).abstractGet();
			assert v.lessOrEqual(r);
			assert u.lessOrEqual(r);
			// widen var region
			MemoryRegion mr = vv.getRight().join(varRegions.get(var));
			assert vv.getRight().lessOrEqual(mr);
			assert varRegions.get(var).lessOrEqual(mr);
			widenedState.setVariableValue(var, r, mr);

			if (Options.failFast.getValue()) {
				// for now only do this check if asked to
				assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
				assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			}
		}
		// Widen memory
		for (EntryIterator<MemoryRegion, Long, T> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			T v = entryIt.getValue();
			int bitWidth = v.getBitWidth();
			T u = other.getMemoryValue(region, offset, bitWidth);
			T r = v.widen(u).abstractGet();
			assert v.lessOrEqual(r);
			assert u.lessOrEqual(r);
			widenedState.setMemoryValue(region, offset, bitWidth, r);

			if (Options.failFast.getValue()) {
				// for now only do this check if asked to
				assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
				assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			}
		}
		logger.debug("Widened " + this + " and " + other + " to " + widenedState);

		// the following two asserts should work, BUT: sometimes it seems to over-approximate constant memory at one
		// state and drop it at another state. then it could be the case that one state references the constant data
		// and the other its over-approximation, causing the asserts to fail
		// maybe an iteration over the second store could fix this?
		if (Options.failFast.getValue()) {
			// for now only do this check if asked to
			assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
		}
		// the next line does not work if join is not a perfect join
		// assert join(other).lessOrEqual(widenedState) : this + " `join` " + other + " = " + join(other) + " !<= " + widenedState;
		return widenedState;
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
		final GenericValuationState<T> result;
		if (isTop() || other.isBot()) {
			result = this;
		} else if (isBot() || other.isTop()) {
			result = other;
		} else if (widen || other.widen) {
			result = widen(other);
		} else {
			result = new GenericValuationState<>(varVal.join(other.varVal), store.join(other.store), factory,
					varRegions.join(other.varRegions), allocationCounter.join(other.allocationCounter), false);
		}
		logger.verbose("Joining " + this + " and " + l + " to " + result);
		return result;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return factory.delegateProjectionFromConcretization(expressions, eval);
	}

	@Override
	public boolean isBot() {
		return varVal.isBot() && store.isBot() && varRegions.isBot();
	}

	@Override
	public boolean isTop() {
		return varVal.isTop() && store.isTop() && varRegions.isTop();
	}

	@Override
	@SuppressWarnings("unchecked")
	public boolean lessOrEqual(LatticeElement l) {
		GenericValuationState<T> other = (GenericValuationState<T>) l;
		// just compare the inner elements, do not use isTop/isBot, they are broken for stores with respect to <=
		boolean vr = varVal.lessOrEqual(other.varVal);
		boolean sr = store.lessOrEqual(other.store);
		boolean rr = varRegions.lessOrEqual(other.varRegions);
		boolean result = vr && sr && rr;
		logger.debug(varVal + " <= " + other.varVal + " = " + vr);
		logger.debug(store + " <= " + other.store + " = " + sr);
		logger.debug(varRegions + " <= " + other.varRegions + " = " + rr);
		logger.debug(this + " <= " + other + " = " + result);
		// see note in partitioned memory
//		if (isBot() || other.isTop()) {
//			assert result;
//		} else if (isTop() || other.isBot()) {
//			assert !result;
//		}
		return result;
	}

	@Override
	public String toString() {
		StringBuilder result = new StringBuilder();
		result.append('[').append(id).append("]:\n");
		result.append("Variables:\n");
		for (Entry<RTLVariable, T> v : new IterableIterator<>(variableIterator())) {
			result.append('\t').append(v.getKey()).append(": ").append(v.getValue()).append('\n');
		}
		result.append("\nMemory:\n");
		for (EntryIterator<MemoryRegion, Long, T> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			T v = entryIt.getValue();
			int bitWidth = v.getBitWidth();
			result.append("\t0x").append(Long.toHexString(offset)).append(" (").append(region).append(") @ ").append(bitWidth).append(": ").append(v).append('\n');
		}
		result.append("\nRegions:\n");
		for (Entry<RTLVariable, MemoryRegion> v : varRegions) {
			result.append('\t').append(v.getKey()).append(": ").append(v.getValue()).append('\n');
		}
		return result.toString();
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

	/**
	 * Get an identifier for an allocation at a location.
	 *
	 * @param loc The location of the allocation.
	 * @return A new identifier for the allocation.
	 */
	int countAllocation(Location loc) {
		return allocationCounter.countAllocation(loc);
	}

	/**
	 * Counter class for allocations.
	 */
	private static final class AllocationCounter {

		/**
		 * Mapping from locations to number of allocations at that location.
		 */
		private final HashMap<Location, Integer> map;

		@SuppressWarnings("unchecked")
		public static AllocationCounter create(AllocationCounter proto) {
			return new AllocationCounter((HashMap<Location, Integer>)proto.map.clone());
		}

		private AllocationCounter(HashMap<Location, Integer> map) {
			this.map = map;
		}

		private AllocationCounter() {
			this(new HashMap<Location, Integer>());
		}

		/**
		 * Count an allocation, returning the next free id at that location.
		 *
		 * @param loc The location of the allocation.
		 * @return The next free id.
		 */
		int countAllocation(Location loc) {
			Integer count = map.get(loc);
			if (count == null) {
				count = 0;
			}
			map.put(loc, count + 1);
			return count;
		}

		/**
		 * Join an allocation counter with another one.
		 *
		 * @param other The other counter.
		 * @return A counter with both allocation maps combined.
		 */
		public AllocationCounter join(AllocationCounter other) {
			Set<Location> keys = new FastSet<>(map.keySet());
			keys.addAll(other.map.keySet());
			HashMap<Location, Integer> newMap = new HashMap<>();
			for (Location key : keys) {
				Integer a = map.get(key);
				Integer b = other.map.get(key);
				newMap.put(key, (a != null ? a : 0) + (b != null ? b : 0) + 1);
			}
			return new AllocationCounter(newMap);
		}
	}
}
