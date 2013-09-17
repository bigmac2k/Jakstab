package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.Set;

import org.jakstab.analysis.AbstractDomainElement;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.util.FastSet;

import cc.sven.intset.*;

public class BDDSet<A extends FiniteOrderedIntegral<A>> implements AbstractDomainElement {

	public IntSet<A> set;
	
	public BDDSet(IntSet<A> init) {
		this.set = init;
	}
	
	@Override
	public Set<RTLNumber> concretize() {
		Set<RTLNumber> outset = new FastSet<RTLNumber>();
		for(A i : set.java()) {
			RTLNumber rtlNum = ExpressionFactory.createNumber(i.toLong(i), i.bits());
			outset.add(rtlNum);
		}
		return outset;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !set.isEmpty();
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		//How I dislike type erasure
		assert l instanceof BDDSet<?>;
		@SuppressWarnings("unchecked")
		BDDSet<A> that = (BDDSet<A>) l;
		return set.subsetOf(that.set);
	}

	@Override
	public boolean isTop() {
		return set.isFull();
	}

	@Override
	public boolean isBot() {
		return set.isEmpty();
	}

	@Override
	public Collection<? extends AbstractDomainElement> readStorePowerSet(
			int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <X extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<X> store, X value) {
		// TODO Auto-generated method stub

	}

	@Override
	public AbstractDomainElement plus(AbstractDomainElement op) {
		assert op instanceof BDDSet<?>;
		@SuppressWarnings("unchecked")
		BDDSet<A> that = (BDDSet<A>) op;
		return new BDDSet<A>(set.plus(that.set));
	}

	@Override
	public AbstractDomainElement negate() {
		if(set.isEmpty())
			return this;
		else {
			//ugly way to get one of A
			A tmp = set.max();
			IntSet<A> one = IntSet$.MODULE$.apply(tmp.one(), tmp, tmp, tmp);
			return new BDDSet<A>(set.bNot().plus(one));
		}
	}

	@Override
	public AbstractDomainElement multiply(AbstractDomainElement op) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractDomainElement bitExtract(int first, int last) {
		//this is totally wrong - should shift every integer to beginning and return different bitwidth
		/*theroretically, we could store the bitwidth in a bdd by having only full length integer in there
		 * then, we would have to rewrite quite a lot of operations such that they behave like there is a true node
		 * even though there is just a "useless" (set = uset) path to a true node
		 * is this equivalent to having more than one terminal? - no caching (sharing) between two different bit lenght would still work
		 * what about storing regions in terminals -> distroys caching
		 */
		
		/*assert last >= first;
		if(set.isEmpty())
			return this;
		else {
			return new BDDSet<A>(set.bitExtract(first, last));
		}*/
		return null;
	}

	@Override
	public AbstractDomainElement signExtend(int first, int last) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractDomainElement zeroFill(int first, int last) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractDomainElement join(LatticeElement l) {
		assert l instanceof BDDSet<?>;
		@SuppressWarnings("unchecked")
		BDDSet<A> that = (BDDSet<A>) l;
		return new BDDSet<A>(set.union(that.set));
	}
}
