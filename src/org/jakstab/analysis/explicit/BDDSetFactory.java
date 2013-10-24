package org.jakstab.analysis.explicit;

import java.util.Collection;

import org.jakstab.analysis.AbstractValueFactory;
import org.jakstab.rtl.expressions.RTLNumber;

public class BDDSetFactory implements AbstractValueFactory<BDDSet> {

	@Override
	public BDDSet createAbstractValue(RTLNumber n) {
		return BDDSet.singleton(n);
	}

	@Override
	public BDDSet createAbstractValue(Collection<RTLNumber> numbers) {
		BDDSet res = null;
		for(RTLNumber rtlnum : numbers) {
			if(res == null)
				res = BDDSet.singleton(rtlnum);
			else {
				BDDSet num = BDDSet.singleton(rtlnum);
				res = res.join(num);
			}
		}
		return res;
	}

	@Override
	public BDDSet createTop(int bitWidth) {
		return BDDSet.topBW(bitWidth);
	}

	@Override
	public BDDSet createTrue() {
		return BDDSet.TRUE;
	}

	@Override
	public BDDSet createFalse() {
		return BDDSet.FALSE;
	}

}
