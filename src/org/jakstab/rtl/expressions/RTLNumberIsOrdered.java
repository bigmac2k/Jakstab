package org.jakstab.rtl.expressions;

import cc.sven.misc.JavaOrdering;

public class RTLNumberIsOrdered extends JavaOrdering<RTLNumber> {
	private static final long serialVersionUID = 1L;
	public int compare(RTLNumber x, RTLNumber y) {
	  long xLong = x.longValue();
	  long yLong = y.longValue();
	  //avoid overflow, otherwise could xLong - yLong
	  if(xLong < yLong)
		  return -1;
	  else if(xLong > yLong)
		  return 1;
	  else return 0;
	}
}
