package org.jakstab.analysis.intervalsets;

import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.analysis.intervals.IntervalElement;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Lattices;

public class IntervalSetElementFactory implements AbstractValueFactory<IntervalSetElement>{

	@Override
	public IntervalSetElement createAbstractValue(RTLNumber n) {
		return new IntervalSetElement(n);
	}

	@Override
	public IntervalSetElement createAbstractValue(Collection<RTLNumber> numbers) {
		List<IntervalSetElement> abstractValues = new LinkedList<IntervalSetElement>();
		for (RTLNumber n : numbers) {
			abstractValues.add(createAbstractValue(n));
		}
		return Lattices.joinAll(abstractValues);
	}

	@Override
	public IntervalSetElement createTop(int bitWidth) {
		return IntervalSetElement.getTop(bitWidth);
	}

	@Override
	public IntervalSetElement createTrue() {
		return new IntervalSetElement(IntervalElement.TRUE);
	}

	@Override
	public IntervalSetElement createFalse() {
		return new IntervalSetElement(IntervalElement.FALSE);
	}

}
