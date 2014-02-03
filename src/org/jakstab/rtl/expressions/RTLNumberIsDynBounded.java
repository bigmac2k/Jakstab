package org.jakstab.rtl.expressions;

import cc.sven.bounded.DynBounded;

public class RTLNumberIsDynBounded implements DynBounded<RTLNumber> {
	public RTLNumber dMinBound(RTLNumber n) {
		int bits = n.getBitWidth();
		//XXX SCM this reverses order for booleans - seems fishy
		if(bits == 1)
			return ExpressionFactory.FALSE;
		if(bits == 64)
			return ExpressionFactory.createNumber(Long.MIN_VALUE, 64);
		return ExpressionFactory.createNumber(-(1L << (bits - 1)), bits);
	}
	public RTLNumber dMaxBound(RTLNumber n) {
		int bits = n.getBitWidth();
		//XXX SCM this reverses order for booleans - seems fishy
		if(bits == 1)
			return ExpressionFactory.TRUE;
		if(bits == 64)
			return ExpressionFactory.createNumber(Long.MAX_VALUE, 64);
		return ExpressionFactory.createNumber((1L << (bits - 1)) - 1, bits);
	}
}
