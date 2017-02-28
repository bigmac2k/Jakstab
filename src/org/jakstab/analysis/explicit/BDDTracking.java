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
import org.jakstab.cfa.PessimisticBasicBlockFactory;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

public class BDDTracking implements ConfigurableProgramAnalysis {
	
	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(BDDTracking.class);
	
	public static void register(AnalysisProperties p) {
		p.setShortHand('z');
		p.setName("Set Address Tracking");
		p.setDescription("Track addresses with a bdd per entry. bdd acts as a combination of set and interval.");
		p.setExplicit(true);
	}
	
	public static JOption<Integer> threshold = JOption.create("bdd-threshold", "k", 3, "Sets the threshold used in merge and prec.");

	public BDDTracking() {}
	
	//public static JOption<Integer> varThreshold = JOption.create("explicit-threshold", "k", 5, "Set the maximum number separate states.");
	//public static JOption<Integer> heapThreshold = JOption.create("heap-threshold", "k", 5, "Explicit threshold for data stored on the heap.");
	
	@Override
	public Set<AbstractState> post(AbstractState state, CFAEdge cfaEdge,
			Precision precision) {
		return ((BDDState) state).abstractPost((RTLStatement) cfaEdge.getTransformer(), precision);
	}

	//XXX scm do we want strenghten? how could anybody be more precise than us.
	@Override
	public AbstractState strengthen(AbstractState s,
			Iterable<AbstractState> otherStates, CFAEdge cfaEdge,
			Precision precision) {
		return s;
	}

	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2,
			Precision precision) {
		//logger.info("merge with precision " + precision + " on states " + s1.getIdentifier() + " and " + s2
		//		.getIdentifier());
		// states equal? s2 is old state (comes from reachedSet)
		if(s2.lessOrEqual(s1)) return s1;
		BDDPrecision prec = (BDDPrecision) precision;
		if(prec.getCount() >= threshold.getValue()) {
			// widen
			logger.info("merge: Will widen now");
			//precision.incRep(); TODO CONT

			BDDState result = ((BDDState) s2).widen((BDDState) s1).join(s1).join(s2);
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
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopJoin(s, reached, precision);
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		// logger.info("prec called on state " + s.getIdentifier());
		logger.debug("prec((" + s + "), (" + precision + "), (" + reached + ")) called");
		//logger.debug("PREC reached size: " + reached.size());
		BDDPrecision prec = (BDDPrecision) precision;
		BDDState newState = (BDDState) s;
		boolean changed = false;
		for(AbstractState state : reached) {
			BDDState bddState = (BDDState) state;
			if(bddState.lessOrEqual(newState)) {
				changed = true;
				break;
			}
		}
		if(!changed) {
			logger.info(" + prec: Nothing changed. How did this happen? ");
			return Pair.create(s, (Precision) new BDDPrecision());
		} else if(prec.getCount() >= threshold.getValue()){
			//XXX: Widen
			/*
			 * go through varmap and memmap, widen every element that needs it...
			 */
			// logger.info(" + prec: resetting precision, since threshold has been reached");
			BDDState out = new BDDState(newState);
			//for(AbstractState state : reached) {
			//	out.widen((BDDState) state); // TODO what was this supposed to do?
			//}
			logger.debug("Widen result: " + out);
			return Pair.create((AbstractState) out, (Precision) new BDDPrecision());
		} else
			// logger.info(" + prec: incr. precision without widening: " + (prec.getCount() + 1));
			return Pair.create(s, (Precision) prec.incCount());
	}

	@Override
	public AbstractState initStartState(Location label) {
		return new BDDState();
	}

	@Override
	public Precision initPrecision(Location location,
			StateTransformer transformer) {
		// TODO Auto-generated method stub
		return new BDDPrecision();
	}

}
