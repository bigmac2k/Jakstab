package org.jakstab.rtl.expressions;

import cc.sven.tlike.Castable;
import cc.sven.misc.Pair;

public class LongBWToRTLNumberCaster implements Castable<Pair<Integer, Long>, RTLNumber> {
	public RTLNumber apply(Pair<Integer, Long> p) {
		return ExpressionFactory.createNumber(p._2(), p._1());
	}
}
