package org.jakstab.analysis.explicit;

import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Pair;

public class BDDTracking implements ConfigurableProgramAnalysis {
	
	public static void register(AnalysisProperties p) {
		p.setShortHand('z');
		p.setName("Set Address Tracking");
		p.setDescription("Track adresses with a bdd per entry. bdd acts as a combination of set and interval.");
		p.setExplicit(true);
	}
	
	public static JOption<Integer> varThreshold = JOption.create("explicit-threshold", "k", 5, "Set the maximum number separate states.");
	public static JOption<Integer> heapThreshold = JOption.create("heap-threshold", "k", 5, "Explicit threshold for data stored on the heap.");
	
	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractState strengthen(AbstractState s,
			Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractState initStartState(Location label) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		// TODO Auto-generated method stub
		return null;
	}

}
