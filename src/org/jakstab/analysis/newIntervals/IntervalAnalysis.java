package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.IterableIterator;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap;
import org.jakstab.util.Pair;

import java.util.Map;
import java.util.Set;

public class IntervalAnalysis implements ConfigurableProgramAnalysis {

    public static void register(AnalysisProperties p) {
        p.setShortHand('j');
        p.setName("Signedness Agnostic Interval analysis");
        p.setDescription("Compute intervals without sign information.");
        p.setExplicit(true);
    }

    private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    public IntervalAnalysis() {
		logger.debug("Started new interval analysis");
    }

    @Override
    public Precision initPrecision(Location location, StateTransformer transformer) {
		logger.debug("Initialized precision");
        return new IntervalPrecision();
    }

    @Override
    public AbstractState initStartState(Location label) {
		logger.debug("Initialized default state");
		return new IntervalValuationState();
    }

    @Override
    public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		if (s2.isTop() || s1.isBot()) {
			return s2;
		}
		if (s1.isTop()) {
			return s1;
		}
		IntervalValuationState current = (IntervalValuationState) s1;
		IntervalValuationState towards = (IntervalValuationState) s2;

		IntervalValuationState widenedState = new IntervalValuationState();

		// Widen variable valuations
		for (Map.Entry<RTLVariable,Interval> entry : new IterableIterator<>(current.variableIterator())) {
			RTLVariable var = entry.getKey();
			Interval v = entry.getValue();
			widenedState.setVariableValue(var, v.widen(towards.getVariableValue(var)));
		}

		// Widen memory
		for (MapMap.EntryIterator<MemoryRegion, Long, Interval> entryIt = current.storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			Interval v = entryIt.getValue();
			int bitWidth = v.getBitWidth();
			widenedState.setMemoryValue(region, offset, bitWidth, v.widen(towards.getMemoryValue(region, offset, bitWidth)));
		}

		return widenedState;
    }

    @Override
    public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision) {
		return Interval.abstractPost((RTLStatement) cfaEdge.getTransformer(), (IntervalValuationState) state);
   }

    @Override
    public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
                                    CFAEdge cfaEdge, Precision precision) {
		logger.debug("Failing to strengthen (not implemented)");
        return s; //TODO actually implement something
    }

    @Override
    public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		logger.debug("Incrementing precision");
		Precision newPrecision = ((IntervalPrecision) precision).inc();
        return Pair.create(s, newPrecision);
    }

    @Override
    public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		logger.debug("Stop-Join");
        return CPAOperators.stopJoin(s, reached, precision);
    }
}
