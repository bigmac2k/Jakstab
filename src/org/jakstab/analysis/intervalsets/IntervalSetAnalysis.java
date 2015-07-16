package org.jakstab.analysis.intervalsets;

import java.util.Set;

import org.jakstab.AnalysisProperties;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.ConfigurableProgramAnalysis;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.ReachedSet;
import org.jakstab.analysis.ValuationState;
import org.jakstab.analysis.intervals.IntervalAnalysis;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

public class IntervalSetAnalysis implements ConfigurableProgramAnalysis{

	public static void register(AnalysisProperties p) {
		p.setShortHand('x');
		p.setName("Interval set analysis");
		p.setDescription("Compute sets of strided intervals with region information.");
		p.setExplicit(true);
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);
	private AbstractValueFactory<IntervalSetElement> valueFactory;

	public IntervalSetAnalysis() {
		valueFactory = new IntervalSetElementFactory();
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return null;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initStartState(org.jakstab.cfa.Location)
	 */
	@Override
	public AbstractState initStartState(Location label) {
		return new ValuationState(valueFactory);
	}


	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge, Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#merge(org.jakstab.analysis.AbstractState, org.jakstab.analysis.AbstractState)
	 */
	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		// TODO Auto-generated method stub
		return false;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s, Precision precision, ReachedSet reached) {
		// TODO Auto-generated method stub
		return null;
	}
}
