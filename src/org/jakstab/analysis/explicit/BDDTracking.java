package org.jakstab.analysis.explicit;

import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.JOption;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.CPAOperators;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Pair;

public class BDDTracking implements ConfigurableProgramAnalysis {
	
	public static void register(AnalysisProperties p) {
		p.setShortHand('z');
		p.setName("Set Address Tracking");
		p.setDescription("Track adresses with a bdd per entry. bdd acts as a combination of set and interval.");
		p.setExplicit(true);
	}
	
	public BDDTracking() {}
	
	//public static JOption<Integer> varThreshold = JOption.create("explicit-threshold", "k", 5, "Set the maximum number separate states.");
	//public static JOption<Integer> heapThreshold = JOption.create("heap-threshold", "k", 5, "Explicit threshold for data stored on the heap.");
	
	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {
		return ((BDDState) state).abstractPost((RTLStatement) cfaEdge.getTransformer(), precision);
	}

	//XXX scm to we want strenghten? how could anybody be more precise than us.
	@Override
	public AbstractState strengthen(AbstractState s,
			Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		return s;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		if(s2.lessOrEqual(s1)) return s1;
		return CPAOperators.mergeSep(s1, s2, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopSep(s, reached, precision);
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new BDDState();
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		// TODO Auto-generated method stub
		return null;
	}

}
