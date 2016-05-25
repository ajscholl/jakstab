package org.jakstab.analysis.newIntervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
import org.jakstab.analysis.newIntervals.statistic.Statistic;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import static org.jakstab.analysis.newIntervals.CongruenceClassInterval.zeroInterval;

public class CongruenceClassIntervalAnalysis extends BaseIntervalAnalysis<CongruenceClassInterval> {

    public static void register(AnalysisProperties p) {
        p.setShortHand('m');
        p.setName("Signedness Agnostic Interval Analysis with Congruence Classes");
        p.setDescription("Compute intervals and congruence classes without needing sign information.");
        p.setExplicit(true);
    }

    private static final Logger logger = Logger.getLogger(CongruenceClassIntervalAnalysis.class);

    public CongruenceClassIntervalAnalysis() {
		super(CongruenceClassIntervalFactory.getFactory());
		Statistic.activateStatistic();
    }

	GenericValuationState<CongruenceClassInterval> assumeNeqVar(RTLVariable var, CongruenceClassInterval newInt, BitNumber val, GenericValuationState<CongruenceClassInterval> newState) {
		Pair<AbstractDomain<CongruenceClassInterval>, MemoryRegion> oldVal = newState.getVariableValue(var);
		CongruenceClassInterval oldInt = oldVal.getLeft().abstractGet();
		oldInt.assertCompatible(newInt);
		if (oldInt.isBot()) {
			// do nothing, is already bottom
			logger.debug("Can not use " + var + " != " + newInt + ", " + var + " is BOT");
		} else if (oldInt.isTop()) {
			// can be anything... but we know it is NOT newInt
			newState.setVariableValue(var, zeroInterval(newInt.range.invert()), oldVal.getRight());
		} else if (val.equals(oldInt.range.minBits)) {
			CongruenceClassInterval newInfo = zeroInterval(IntervalElement.interval(oldInt.range.minBits.inc(), oldInt.range.maxBits));
			newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
		} else if (val.equals(oldInt.range.maxBits)) {
			CongruenceClassInterval newInfo = zeroInterval(IntervalElement.interval(oldInt.range.minBits, oldInt.range.maxBits.dec()));
			newState.setVariableValue(var, oldInt.meet(newInfo), oldVal.getRight());
		} else {
			logger.debug("Can not use information in " + var + ' ' + oldInt + " != " + newInt);
		}
		return newState;
	}
}
