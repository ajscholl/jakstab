package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
import org.jakstab.analysis.newIntervals.statistic.Statistic;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import static org.jakstab.analysis.newIntervals.IntervalElement.interval;

/**
 * Implementation for the analysis for intervals.
 *
 * @author A. J. Scholl
 */
public class IntervalAnalysis extends BaseIntervalAnalysis<IntervalElement> {

	/**
	 * Called by reflection code inside Jakstab. Registers this analysis.
	 *
	 * @param p The properties to register with.
	 */
    public static void register(AnalysisProperties p) {
        p.setShortHand('j');
        p.setName("Signedness Agnostic Interval analysis");
        p.setDescription("Compute intervals without sign information.");
        p.setExplicit(true);
    }

	/**
	 * Logger.
	 */
    private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

	/**
	 * Create a new analysis with the correct factory.
	 */
    public IntervalAnalysis() {
		super(IntervalElementFactory.getFactory());
		Statistic.activateStatistic();
    }

	@Override
	GenericValuationState<IntervalElement> assumeNeqVar(RTLVariable var, IntervalElement newInt, BitNumber val, GenericValuationState<IntervalElement> newState) {
		Pair<AbstractDomain<IntervalElement>, MemoryRegion> oldVal = newState.getVariableValue(var);
		IntervalElement oldInt = oldVal.getLeft().abstractGet();
		oldInt.assertCompatible(newInt);
		if (oldInt.isBot()) {
			// do nothing, is already bottom
			logger.debug("Can not use " + var + " != " + newInt + ", " + var + " is BOT");
		} else if (oldInt.isTop()) {
			// can be anything... but we know it is NOT newInt
			newState.setVariableValue(var, newInt.invert(), oldVal.getRight());
		} else if (val.equals(oldInt.minBits)) {
			IntervalElement newInfo = interval(oldInt.minBits.inc(), oldInt.maxBits);
			newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
		} else if (val.equals(oldInt.maxBits)) {
			IntervalElement newInfo = interval(oldInt.minBits, oldInt.maxBits.dec());
			newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
		} else {
			logger.debug("Can not use information in " + var + ' ' + oldInt + " != " + newInt);
		}
		return newState;
	}
}
