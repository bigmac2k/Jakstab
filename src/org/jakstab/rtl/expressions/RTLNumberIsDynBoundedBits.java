package org.jakstab.rtl.expressions;

import cc.sven.bounded.DynBoundedBits;

public class RTLNumberIsDynBoundedBits implements DynBoundedBits<RTLNumber> {
  public int dBits(RTLNumber rtlnum) {
	  return rtlnum.getBitWidth();
  }
}
