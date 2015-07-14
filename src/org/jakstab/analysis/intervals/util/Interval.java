package org.jakstab.analysis.intervals.util;

public class Interval {
	private long lowerBound;
	private long upperBound;
	
	private Interval.TYPE type;
	
	// for error handeling on call site
	public Interval() {
		lowerBound = 0;
		upperBound = 0;
		type = Interval.TYPE.PP;
	}
	
	public Interval(long a, long b) throws IllegalArgumentException {
		if (a > b) {
			throw new IllegalArgumentException("Constructor: lower bound " + a + " is greater than upper bound " + b);
		}
		
		lowerBound = a;
		upperBound = b;
		
		if ((a >= 0) && (b >= 0)) {
			type = Interval.TYPE.PP;
		} else if ((a < 0) && (b >= 0)) {
			type = Interval.TYPE.NP;
		} else if ((a < 0) && (b < 0)) {
			type = Interval.TYPE.NN;
		} else {
			throw new IllegalArgumentException("Could not determin Interval type for a = " + a + " b = " + b);
		}
	}

	public void setBounds(long a, long b) {
		if (a > b) {
			throw new IllegalArgumentException("setBounds: lower bound " + a + " is greater than upper bound " + b);
		}
		
		lowerBound = a;
		upperBound = b;
		
		if ((a >= 0) && (b >= 0)) {
			type = Interval.TYPE.PP;
		} else if ((a < 0) && (b >= 0)) {
			type = Interval.TYPE.NP;
		} else if ((a < 0) && (b < 0)) {
			type = Interval.TYPE.NN;
		} else {
			throw new IllegalArgumentException("Could not determin Interval type for a = " + a + " b = " + b);
		}
	}
	
	public long getLowerBound() {
		return lowerBound;
	}

	public long getUpperBound() {
		return upperBound;
	}
	
	public long l() {
		return lowerBound;
	}
	
	public long g() {
		return upperBound;
	}

	public Interval.TYPE getType() {
		return type;
	}
	
	public String toString() {
		return "[" + lowerBound + ".." + upperBound + "]";
	}
	
	public static TYPE DetermineType(long a, long b) throws IllegalArgumentException {
		if (a > b) {
			throw new IllegalArgumentException("Illegal arguments: [" + a + ".." + b + "]");
		}
		
		if ((a >= 0) && (b >= 0)) {
			return Interval.TYPE.PP;
		} else if ((a < 0) && (b >= 0)) {
			return Interval.TYPE.NP;
		} else if ((a < 0) && (b < 0)) {
			return Interval.TYPE.NN;
		} else {
			throw new IllegalArgumentException("Could not determin Interval type for [" + a + ".." + b + "]");
		}
	}

	public enum TYPE {
		PP,
		NP,
		NN
	}
}
