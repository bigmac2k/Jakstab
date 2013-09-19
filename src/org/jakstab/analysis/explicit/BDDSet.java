package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.Set;

import org.jakstab.analysis.AbstractDomainElement;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.LongBWToRTLNumberCaster;
import org.jakstab.rtl.expressions.RTLNumberToLongBWCaster;
import org.jakstab.rtl.expressions.RTLNumberIsDynBoundedBits;
import cc.sven.integral.JLongIsIntegral;
import cc.sven.bounded.JLongIsBounded;
import cc.sven.bounded.JLongIsBoundedBits;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.util.FastSet;

import cc.sven.intset.FiniteOrderedIntegral;
import cc.sven.tlike.*;

/* TODO extend this to something that not only contains RTLNumbers, but essentially (Region, RTLNumber)
 * futher more, each Region may have another bit width.
 * Therefore: Map(Region -> BitWidth), Map(Region, RTLNumber)?
 */
public class BDDSet implements AbstractDomainElement {

	public IntLikeSet<Long, RTLNumber> set;
	
	public BDDSet(IntLikeSet<Long, RTLNumber> init) {
		this.set = init;
	}
	
	@Override
	public Set<RTLNumber> concretize() {
		Set<RTLNumber> outset = new FastSet<RTLNumber>();
		for(RTLNumber i : set.java()) {
			outset.add(i);
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
		@SuppressWarnings("unchecked")
		BDDSet that = (BDDSet) l;
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
		return null;
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		IntLikeSet<Long, RTLNumber> resultSet = null;
		for (RTLNumber rtlnum : set.java()) {
			BDDSet res = (BDDSet) store.get(MemoryRegion.GLOBAL, rtlnum.longValue(), set.bits());
			if(resultSet == null) {
				resultSet = IntLikeSet$.MODULE$.applyJLong(res.set.bits(), new RTLNumberIsDynBoundedBits(), new RTLNumberToLongBWCaster(), new LongBWToRTLNumberCaster());
			}
			resultSet = resultSet.add(rtlnum);
		}
		return new BDDSet(resultSet);
	}

	@Override
	public <X extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<X> store, X value) {
		// TODO Auto-generated method stub

	}

	@Override
	public AbstractDomainElement plus(AbstractDomainElement op) {
		assert op instanceof BDDSet;
		@SuppressWarnings("unchecked")
		BDDSet that = (BDDSet) op;
		return new BDDSet(set.plus(that.set));
	}

	@Override
	public AbstractDomainElement negate() {
		return new BDDSet(set.negate());
	}

	@Override
	public AbstractDomainElement multiply(AbstractDomainElement op) {
		assert false : "Not implemented";
		return null;
	}

	@Override
	public AbstractDomainElement bitExtract(int first, int last) {
		return new BDDSet(set.bitExtract(last, first));
	}

	@Override
	public AbstractDomainElement signExtend(int first, int last) {
		return new BDDSet(set.signExtend(last, first));
	}

	@Override
	public AbstractDomainElement zeroFill(int first, int last) {
		return new BDDSet(set.zeroFill(last, first));
	}

	@Override
	public AbstractDomainElement join(LatticeElement l) {
		assert l instanceof BDDSet;
		@SuppressWarnings("unchecked")
		BDDSet that = (BDDSet) l;
		return new BDDSet(set.union(that.set));
	}
}
