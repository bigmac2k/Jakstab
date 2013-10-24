package org.jakstab.rtl.expressions;

import cc.sven.tlike.Castable;
import cc.sven.tlike.NBitLong;
import cc.sven.misc.Pair;
import cc.sven.misc.Pair$;

public class RTLNumberToLongBWCaster implements Castable<RTLNumber, Pair<Integer, Long>> {
  public Pair<Integer, Long> apply(RTLNumber rtlnum) {
	  long value = NBitLong.signContract(rtlnum.getBitWidth(), rtlnum.longValue());
	  return Pair$.MODULE$.apply(rtlnum.getBitWidth(), value);
  }
}