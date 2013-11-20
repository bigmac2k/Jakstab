package org.jakstab.analysis.explicit;

import org.jakstab.analysis.Precision;

public class BDDPrecision implements Precision {
	private int count;
	public BDDPrecision() {
		this.count = 0;
	}
	private BDDPrecision(int c) {
		this.count = c;
	}
	public BDDPrecision copy() {
		return new BDDPrecision(count);
	}
	public BDDPrecision inc() {
		return new BDDPrecision(count + 1);
	}
	public int getCount() {
		return count;
	}
	@Override
	public String toString() {
		return "Count: " + ((Integer) count).toString();
	}
}
