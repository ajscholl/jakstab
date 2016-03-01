package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.analysis.*;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import java.util.Set;

public class IntervalAnalysis implements ConfigurableProgramAnalysis {

    public static void register(AnalysisProperties p) {
        p.setShortHand('j');
        p.setName("Signedness Agnostic Interval analysis");
        p.setDescription("Compute intervals without sign information.");
        p.setExplicit(true);
    }

	public static JOption<Integer> threshold = JOption.create("interval-threshold", "k", 3, "Sets the threshold used in merge and prec.");

    @SuppressWarnings("unused")
    private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    public IntervalAnalysis() {

    }

    @Override
    public Precision initPrecision(Location location, StateTransformer transformer) {
        return new IntervalPrecision();
    }

    @Override
    public AbstractState initStartState(Location label) {
        return Interval.mkDefaultInterval();
    }

    @Override
    public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
        logger.debug("merge with precision " + precision + " on states " + s1.getIdentifier() + " and " + s2.getIdentifier());
        //states equal? s2 is old state (comes from reachedSet)
        if(s2.lessOrEqual(s1)) {
            return s1;
        }
        IntervalPrecision prec = (IntervalPrecision) precision;
        if(prec.getCount() >= threshold.getValue()) {
            //widen
            logger.debug("Will widen now");
            Interval result = ((Interval) s2).widen((Interval) s1).join(s1).join(s2); // TODO can we remove the joins? the assert in widen should ensure this
            logger.debug("s1: " + s1);
            logger.debug("s2: " + s2);
            logger.debug("result: " + result);
            logger.debug("check: " + CPAOperators.mergeJoin(s1, s2, precision));
            assert(CPAOperators.mergeJoin(s1, s2, precision).lessOrEqual(result));
            return result;
        } else {
            return CPAOperators.mergeJoin(s1, s2, precision);
        }
    }

    @Override
    public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision) {
		return ((Interval) state).abstractPost((RTLStatement) cfaEdge.getTransformer(), precision);
   }

    @Override
    public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
                                    CFAEdge cfaEdge, Precision precision) {
        return s; //TODO actually implement something
    }

    @Override
    public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		Precision newPrecision = ((IntervalPrecision) precision).inc();
        return Pair.create(s, newPrecision);
    }

    @Override
    public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
        return CPAOperators.stopJoin(s, reached, precision);
    }
}
