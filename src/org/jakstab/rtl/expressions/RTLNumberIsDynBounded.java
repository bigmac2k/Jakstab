package org.jakstab.rtl.expressions;

import cc.sven.bounded.DynBounded;

public class RTLNumberIsDynBounded implements DynBounded<RTLNumber> {
	public RTLNumber dMinBound(RTLNumber n) {
		int bits = n.getBitWidth();
		long l = 0;
		if(bits == 1)
			return ExpressionFactory.createNumber(-1, 1);
		for(int i = 0; i < bits - 1; bits += 1) {
			l |= (1L << i);
		}
		return ExpressionFactory.createNumber(l, bits);
	}
	public RTLNumber dMaxBound(RTLNumber n) {
		int bits = n.getBitWidth();
		if(bits == 1)
			return ExpressionFactory.createNumber(0, 1);
		long l = 1L << (bits - 1);
		return ExpressionFactory.createNumber(l, bits);
	}
}
