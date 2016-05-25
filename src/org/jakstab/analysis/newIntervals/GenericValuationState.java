package org.jakstab.analysis.newIntervals;

import org.jakstab.Options;
import org.jakstab.analysis.*;
import org.jakstab.analysis.newIntervals.abstracted.*;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.ControlFlowGraph;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.RTLLabel;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLMemoryLocation;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.BasicBlock;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.*;
import org.jakstab.util.MapMap.EntryIterator;

import java.io.FileOutputStream;
import java.io.OutputStream;
import java.util.*;
import java.util.Map.Entry;

public final class GenericValuationState<T extends AbstractDomain<T> & Boxable<T>> implements AbstractState, AbstractValuationState<T> {

	private static final Logger logger = Logger.getLogger(GenericValuationState.class);

	private static long maxStateId = 0L;

	final long id;
	private final VariableValuation<T> varVal;
	final PartitionedMemory<T> store;
	private final AbstractDomainFactory<T> factory;
	private final AbstractEvaluator<T> eval;
	final AllocationCounter allocationCounter;
	private final VariableRegion varRegions;

	private final static Set<GenericValuationState<?>> allStates = Collections.newSetFromMap(new WeakHashMap<GenericValuationState<?>, Boolean>());

	GenericValuationState(GenericValuationState<T> proto, RTLStatement stmt) {
		this(new VariableValuation<>(proto.varVal),
			 new PartitionedMemory<>(proto.store),
			 proto.factory,
			 new VariableRegion(proto.varRegions),
			 AllocationCounter.create(proto.allocationCounter),
				new TraceNode(stmt, proto.trace), stmt != null ? stmt.getLabel() : null);
	}

	GenericValuationState(AbstractDomainFactory<T> factory) {
		this(new VariableValuation<>(factory), new PartitionedMemory<>(factory), factory, new VariableRegion(), new AllocationCounter(), null, null);
	}

	private GenericValuationState(VariableValuation<T> varVal,
								  PartitionedMemory<T> store,
								  AbstractDomainFactory<T> factory,
								  VariableRegion varRegions,
								  AllocationCounter allocationCounter,
								  TraceNode t,
								  RTLLabel lbl) {
		assert varVal != null;
		assert store != null;
		id = maxStateId;
		incId();
		this.varVal = varVal;
		this.store = store;
		this.factory = factory;
		this.varRegions = varRegions;
		this.allocationCounter = allocationCounter;
		trace = t;
		if (trace != null) {
			trace.setState(this);
		}
		eval = new AbstractEvaluator<>(factory, this);
		allStates.add(this);
		if (lbl != null) {
			recordState(lbl, this);
		}
	}

	private static void incId() {
		maxStateId++;
	}

	public T abstractEval(RTLExpression e) {
		return eval.evalExpression(e).abstractGet();
	}

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

	void setMemoryValue(T address, T value, MemoryRegion region) {
		assert region != MemoryRegion.TOP;
		int bitWidth = value.getBitWidth();
		if (address.hasUniqueConcretization()) {
			setMemoryValue(region, address.getUniqueConcretization().zExtLongValue(), bitWidth, value);
		} else if (address.isTop()) {
			if (!store.isTop()) {
				assert !Options.failFast.getValue() : "Overwritten too much memory (" + address + ") when writing " + address + " with value " + value + " with memory " + store;
				for (EntryIterator<MemoryRegion, Long, T> entryIt = storeIterator(); entryIt.hasEntry(); entryIt.next()) {
					// TODO region
					// TODO what does TODO region mean?
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

	private void setMemoryValue(MemoryRegion region, long offset, int bitWidth, T value) {
		if (region.equals(MemoryRegion.TOP)) {
			store.setTop(region);
		} else {
			store.set(region, offset, bitWidth, value);
		}
	}

	void setVariableValue(RTLVariable var, T value, MemoryRegion region) {
		logger.debug("Setting " + var + " to " + value + '/' + region + " in state " + id);
		varVal.set(var, value);
		varRegions.set(var, region);
	}

	public T getMemoryValue(RTLMemoryLocation address) {
		logger.debug("Getting memory value at " + address);
		T addressValue = eval.evalExpression(address.getAddress()).abstractGet();
		MemoryRegion region = getRegion(address);
		logger.debug("Address evaluated to " + addressValue + " in region " + region);
		return getMemoryValue(addressValue, region, address.getBitWidth());
	}

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

	private T getMemoryValue(MemoryRegion region, long offset, int bitWidth) {
		if (region.equals(MemoryRegion.TOP)) {
			return factory.createTop(bitWidth);
		}
		return store.get(region, offset, bitWidth);
	}

	public Pair<AbstractDomain<T>, MemoryRegion> getVariableValue(RTLVariable var) {
		return new Pair<>(varVal.get(var).abstractBox(), varRegions.get(var));
	}

	private Iterator<Entry<RTLVariable, T>> variableIterator() {
		return varVal.iterator();
	}

	private EntryIterator<MemoryRegion, Long, T> storeIterator() {
		return store.entryIterator();
	}

	final TraceNode trace;

	static class TraceNode {
		final RTLStatement stmt;
		String state;
		final TraceNode parent;
		final TraceNode merged;
		static int next = 0;

		TraceNode(RTLStatement s, TraceNode p) {
			stmt = s;
			parent = p;
			merged = null;
		}

		TraceNode(TraceNode p, TraceNode m) {
			stmt = null;
			parent = p;
			merged = m;
		}

		public void setState(GenericValuationState<?> st) {
			this.state = st.toString();
		}

		static void mkEdge(int a, int b, StringBuilder file) {
			file.append('"').append(a).append("\" -> \"").append(b).append("\" [color=\"#000000\"];\n");
		}

		static void mkNode(int a, RTLStatement cont, String state, StringBuilder file) {
			String contStr;
			if (cont == null) {
				contStr = "join";
			} else {
				contStr = cont.toString();
			}
			file.append('"').append(a).append("\"[label=\"").append(contStr).append("\n\n").append(state).append("\\n\"];\n");
		}

		static int printTrace(TraceNode node, Map<TraceNode, Integer> map, StringBuilder file, StringBuilder edges) {
			if (map.containsKey(node)) {
				return map.get(node);
			}
			int nodeId = next;
			next++;
			map.put(node, nodeId);
			mkNode(nodeId, node.stmt, node.state, file);
			if (node.parent != null) {
				int parentId = printTrace(node.parent, map, file, edges);
				mkEdge(parentId, nodeId, edges);
			}
			if (node.merged != null) {
				int mergedId = printTrace(node.merged, map, file, edges);
				mkEdge(mergedId, nodeId, edges);
			}
			return nodeId;
		}

		static void showTrace() {
			Runtime.getRuntime().gc();
			StringBuilder dotFile = new StringBuilder();
			dotFile.append("digraph G {\n");
			dotFile.append("node[shape=rectangle,style=filled,fillcolor=lightsteelblue,color=lightsteelblue]\n");
			dotFile.append("bgcolor=\"transparent\"\n");
			dotFile.append("graph [label=\"Trace\", labelloc=t, fontsize=35, pad=30];\n");
			StringBuilder edges = new StringBuilder();
			Map<TraceNode, Integer> map = new HashMap<>();
			for (GenericValuationState<?> s : allStates) {
				if (s.trace != null) {
					printTrace(s.trace, map, dotFile, edges);
				}
			}
			dotFile.append(edges);
			dotFile.append("}\n");
			try {
				byte[] data = dotFile.toString().getBytes();
				try (OutputStream os = new FileOutputStream("debug.dot")) {
					os.write(data);
				}
				try (OutputStream s = new ProcessBuilder("xdot", "-").start().getOutputStream()) {
					s.write(data);
				}
			} catch (Exception e) {
				e.printStackTrace();
			}
		}
	}

	private final static Map<RTLLabel, Pair<Integer, Map<String, Integer>>> labelMap = new HashMap<>();

	static void recordState(RTLLabel lbl, GenericValuationState<?> s) {
		String str = s.toString();
		if (labelMap.containsKey(lbl)) {
			Pair<Integer, Map<String, Integer>> p = labelMap.get(lbl);
			if (!p.getRight().containsKey(str)) {
				p.getRight().put(str, p.getLeft());
				labelMap.put(lbl, new Pair<>(p.getLeft() + 1, p.getRight()));
			}
		} else {
			Map<String, Integer> map = new HashMap<>();
			map.put(str, 0);
			labelMap.put(lbl, new Pair<>(1, map));
		}
	}

	private static void mkRecoredEdge(CFAEdge edge, StringBuilder file) {
		file.append('"').append(edge.getSource().getLabel()).append("\" -> \"").append(edge.getTarget().getLabel()).append("\" [color=\"#000000\"];\n");
	}

	private static void mkRecordedNode(Location loc, BasicBlock block, Map<String, Integer> cont, StringBuilder file, StringBuilder edges) {
		StringBuilder contStr = new StringBuilder();
		contStr.append(loc.getLabel()).append("\\n");
		if (block != null) {
			for (RTLStatement stmt : block) {
				contStr.append(stmt).append("\\n");
			}
		}

		Map<Integer, String> mmap = new TreeMap<>();
		List<Integer> keys = new ArrayList<>(cont.values());
		Collections.sort(keys);
		int minVal = -1;
		if (keys.size() > 5) {
			minVal = keys.get(keys.size() - 5);
		}
		for (Entry<String, Integer> entry : cont.entrySet()) {
			if (entry.getValue() > minVal) {
				mmap.put(entry.getValue(), entry.getKey());
			}
		}

		file.append('"').append(loc.getLabel()).append("\"[label=\"").append(contStr).append("\\n\"];\n");

		int i = 0;
		for (String s : mmap.values()) {
			contStr = new StringBuilder();
			for (String t : s.split("\n")) {
				contStr.append("\\n").append(t);
			}
			contStr.append("\\n");
			file.append('"').append(loc.getLabel()).append('$').append(i).append("\"[label=\"").append(contStr).append("\\n\"];\n");
			edges.append('"').append(loc.getLabel()).append("\" -> \"").append(loc.getLabel()).append('$').append(i).append("\" [color=\"#000000\"];\n");
			i++;
		}
	}

	private static void printRecordedTrace(ControlFlowGraph cfg, Location loc, Set<Location> visited, StringBuilder file, StringBuilder edges) {
		if (visited.contains(loc)) {
			return;
		}
		visited.add(loc);
		mkRecordedNode(loc, cfg.getBasicBlock(loc), labelMap.get(loc.getLabel()).getRight(), file, edges);
		for (CFAEdge edge : cfg.getOutEdges(loc)) {
			mkRecoredEdge(edge, edges);
			printRecordedTrace(cfg, edge.getTarget(), visited, file, edges);
		}
	}

	public static void showRecordedState(ControlFlowGraph cfg) {
		System.out.println("Writing debug data");
		StringBuilder dotFile = new StringBuilder();
		dotFile.append("digraph G {\n");
		dotFile.append("node[shape=rectangle,style=filled,fillcolor=lightsteelblue,color=lightsteelblue]\n");
		dotFile.append("bgcolor=\"transparent\"\n");
		dotFile.append("graph [label=\"Trace\", labelloc=t, fontsize=35, pad=30];\n");
		StringBuilder edges = new StringBuilder();
		printRecordedTrace(cfg, cfg.getEntryPoint(), new HashSet<Location>(), dotFile, edges);
		dotFile.append(edges);
		dotFile.append("}\n");
		try {
			byte[] data = dotFile.toString().getBytes();
			try (OutputStream os = new FileOutputStream("debug2.dot")) {
				os.write(data);
			}
			try (OutputStream s = new ProcessBuilder("xdot", "-").start().getOutputStream()) {
				s.write(data);
			}
		} catch (Exception e) {
			e.printStackTrace();
		}
	}

	GenericValuationState<T> widen(GenericValuationState<T> other) {
		GenericValuationState<T> widenedState = new GenericValuationState<>(factory);
		// Widen variable valuations
		for (Entry<RTLVariable,T> entry : new IterableIterator<>(variableIterator())) {
			RTLVariable var = entry.getKey();
			T v = entry.getValue();
			Pair<AbstractDomain<T>, MemoryRegion> vv = other.getVariableValue(var);
			T u = vv.getLeft().abstractGet();
			T r = v.widen(u).abstractGet();
			if (var.toString().equals("eax")) {
				logger.error("Widening EAX from " + v + " and " + u + " to " + r);
			}
			assert v.lessOrEqual(r);
			assert u.lessOrEqual(r);
			// widen var region
			MemoryRegion mr = vv.getRight().join(varRegions.get(var));
			assert vv.getRight().lessOrEqual(mr);
			assert varRegions.get(var).lessOrEqual(mr);
			widenedState.setVariableValue(var, r, mr);

			// TODO remove? well, for fail-fast and debugging this may be good
			//if (Options.failFast.getValue()) {
				// for now only do this check if asked to
				assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
				assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			//}
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

			// TODO remove? well, for fail-fast and debugging this may be good
			//if (Options.failFast.getValue()) {
				// for now only do this check if asked to
				assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
				assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			//}
		}
		logger.debug("Widened " + this + " and " + other + " to " + widenedState);

		// TODO the following two asserts should work, BUT: sometimes it seems to over-approximate constant memory at one
		// state and drop it at another state. then it could be the case that one state references the constant data
		// and the other its over-approximation, causing the asserts to fail
		// maybe an iteration over the second store could fix this?
		//if (Options.failFast.getValue()) {
			// for now only do this check if asked to
			assert lessOrEqual(widenedState) : this + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
			assert other.lessOrEqual(widenedState) : other + " is not less or equal than " + widenedState + ", but widen should be an upper bound operator";
		//}
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
		} else {
			result = new GenericValuationState<>(varVal.join(other.varVal), store.join(other.store), factory,
					varRegions.join(other.varRegions), allocationCounter.join(other.allocationCounter), new TraceNode(trace, other.trace), null);
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
		return false;
	}

	@Override
	public boolean isTop() {
		return varVal.isTop() && store.isTop() && varRegions.isTop();
	}

	@Override
	@SuppressWarnings("unchecked")
	public boolean lessOrEqual(LatticeElement l) {
		GenericValuationState<T> other = (GenericValuationState<T>) l;
		// just compare the inner elements, do not use isTop/isBot, it is not necessary
		boolean vr = varVal.lessOrEqual(other.varVal);
		boolean sr = store.lessOrEqual(other.store);
		boolean rr = varRegions.lessOrEqual(other.varRegions);
		boolean result = vr && sr && rr;
		logger.debug(varVal + " <= " + other.varVal + " = " + vr);
		logger.debug(store + " <= " + other.store + " = " + sr);
		logger.debug(varRegions + " <= " + other.varRegions + " = " + rr);
		logger.debug(this + " <= " + other + " = " + result);
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

	static final class AllocationCounter {
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

		int countAllocation(Location loc) {
			Integer count = map.get(loc);
			if (count == null) {
				count = 0;
			}
			map.put(loc, count + 1);
			return count;
		}

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
