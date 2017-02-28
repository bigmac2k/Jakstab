package org.jakstab.analysis.explicit;

import org.jakstab.analysis.Precision;
import org.jakstab.util.Logger;

public class BDDPrecision implements Precision {
	private int count;
	private int rep;

	private static final Logger logger = Logger.getLogger(BDDPrecision.class);

	public BDDPrecision() {
		this.count = 0;
		this.rep = 0;
	}
	public BDDPrecision(int c, int r) {
		this.count = c;
		this.rep = r;
	}
	public BDDPrecision copy() {
		return new BDDPrecision(count, rep);
	}
	public BDDPrecision incCount() {
		return new BDDPrecision(count + 1, rep);
	}
	public int getCount() {
		return count;
	}
	public BDDPrecision zero() {
		return new BDDPrecision();
	}
	public BDDPrecision incRep() {
		logger.info(" + incr. rep");
		return new BDDPrecision(count, rep + 1);
	}
	public int getRep(){
		return rep;
	}

	@Override
	public String toString() {
		return "Count: " + ((Integer) count).toString() + ", rep: " + ((Integer) rep).toString();
	}
}
