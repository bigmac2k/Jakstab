package org.jakstab.analysis.intervals.util;

public class BitwiseOperations {

	
	
	public static Interval XOR(Interval x, Interval y) {
		return XOR(x.l(), x.g(), y.l(), y.g());
	}
	
	
	public static Interval XOR (long a, long b, long c, long d) throws IllegalArgumentException {
		Interval.TYPE xType = Interval.DetermineType(a, b);
		Interval.TYPE yType = Interval.DetermineType(c, d);
		
		long upper;
		long lower;
		
		//System.out.println("TYPE: " + xType + " " + yType);
		if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case PP PP");
			lower = UNSAVE_LOWER_XOR(a, b, c, d);
			upper = UNSAVE_UPPER_XOR(a, b, c, d);
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case PP NP");
			lower = UNSAVE_LOWER_XOR(a, b, c, -1);
			upper = UNSAVE_UPPER_XOR(a, b, 0, d);
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case PP NN");
			lower = UNSAVE_LOWER_XOR(a, b, c, d);
			upper = UNSAVE_UPPER_XOR(a, b, c, d);
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NP NP");
			lower = min(UNSAVE_LOWER_XOR(a, -1, 0, d), UNSAVE_LOWER_XOR(0, b, c, -1));
			upper = max(UNSAVE_UPPER_XOR(0, b, 0, d), UNSAVE_UPPER_XOR(a, -1, c, -1));
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NP NN");
			lower = UNSAVE_LOWER_XOR(0, b, c, d);
			upper = UNSAVE_UPPER_XOR(a, -1, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_XOR(a, b, c, d);
			upper = UNSAVE_UPPER_XOR(a, b, c, d);
		} 
		//'Mirrored cases'
		else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_XOR(a, -1, c, d);
			upper = UNSAVE_UPPER_XOR(0, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_XOR(a, b, c, d);
			upper = UNSAVE_UPPER_XOR(a, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_XOR(a, b, 0, d);
			upper = UNSAVE_UPPER_XOR(a, b, c, -1);
		} 
		
		else {
			throw new IllegalArgumentException("Could not determine Case for " + xType + " - " + yType + "\t[" + a + ".." + b + " [" + c + ".." + d + "]");
		}
		return new Interval(lower, upper);
	}
	
	public static Interval OR(Interval x, Interval y) {
		return OR(x.l(), x.g(), y.l(), y.g());
	}
	
	public static Interval OR(long a, long b, long c, long d) {
		Interval.TYPE xType = Interval.DetermineType(a, b);
		Interval.TYPE yType = Interval.DetermineType(c, d);
		
		long upper;
		long lower;
		
		if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case PP PP");
			lower = UNSAVE_LOWER_OR(a, b, c, d);
			upper = UNSAVE_UPPER_OR(a, b, c, d);
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case PP NP");
			lower = UNSAVE_LOWER_OR(a, b, c, -1);
			upper = UNSAVE_UPPER_OR(a, b, 0, d);
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case PP NN");
			lower = UNSAVE_LOWER_OR(a, b, c, d);
			upper = UNSAVE_UPPER_OR(a, b, c, d);
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NP NP");
			lower = min(a, c);
			upper = UNSAVE_UPPER_OR(0, b, 0, d);
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NP NN");
			lower = c;
			upper = -1;
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_OR(a, b, c, d);
			upper = UNSAVE_UPPER_OR(a, b, c, d);
		} 
		//'Mirrored cases'
		else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_OR(a, -1, c, d);
			upper = UNSAVE_UPPER_OR(0, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_OR(a, b, c, d);
			upper = UNSAVE_UPPER_OR(a, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NN NN");
			lower = a;
			upper = -1;
		} 
		
		else {
			throw new IllegalArgumentException("Could not determine Case for " + xType + " - " + yType + "\t[" + a + ".." + b + " [" + c + ".." + d + "]");
		}
		
		return new Interval(lower, upper);
	}
	
	public static Interval AND (Interval x, Interval y) {
		return AND(x.l(), x.g(), y.l(), y.g());
	}
	
	public static Interval AND (long a, long b, long c, long d) {
		Interval.TYPE xType = Interval.DetermineType(a, b);
		Interval.TYPE yType = Interval.DetermineType(c, d);
		
		long upper;
		long lower;
		
		if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case PP PP");
			lower = UNSAVE_LOWER_AND(a, b, c, d);
			upper = UNSAVE_UPPER_AND(a, b, c, d);
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case PP NP");
			lower = 0;
			upper = b;
		} else if ((xType == Interval.TYPE.PP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case PP NN");
			lower = UNSAVE_LOWER_AND(a, b, c, d);
			upper = UNSAVE_UPPER_AND(a, b, c, d);
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NP NP");
			lower = UNSAVE_LOWER_AND(a, -1, c, -1);
			upper = max(b, d);
		} else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NP NN");
			lower = UNSAVE_LOWER_AND(a, -1, c, d);
			upper = UNSAVE_UPPER_AND(0, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NN)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_AND(a, b, c, d);
			upper = UNSAVE_UPPER_AND(a, b, c, d);
		} 
		//'MirrANDed cases'
		else if ((xType == Interval.TYPE.NP) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = 0;
			upper = d;
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.PP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_AND(a, b, c, d);
			upper = UNSAVE_UPPER_AND(a, b, c, d);
		} else if ((xType == Interval.TYPE.NN) && (yType == Interval.TYPE.NP)) {
			//System.out.println("case NN NN");
			lower = UNSAVE_LOWER_AND(a, b, c, -1);
			upper = UNSAVE_UPPER_AND(a, b, 0, d);
		} 
		
		else {
			throw new IllegalArgumentException("Could not determine Case for " + xType + " - " + yType + "\t[" + a + ".." + b + " [" + c + ".." + d + "]");
		}
		
		return new Interval(lower, upper);
	}
	
	
	public static Interval naivOR(Interval x, Interval y) throws IllegalArgumentException {
		long l = x.l() | y.l();
		long g = x.g() | y.g();
		long tmp = 0;
		for (long m = x.l(); m <= x.g(); m++) {
			for (long n = y.l(); n <= y.g(); n++) {
				tmp = m | n;
				if (tmp > g) {
					g = tmp;
				}
				if (tmp < l) {
					l = tmp;
				}
			}
		}
		return new Interval(l, g);
	}
	
	public static Interval naivXOR(Interval x, Interval y) throws IllegalArgumentException {
		long l = x.l() ^ y.l();
		long g = x.g() ^ y.g();
		long tmp = 0;
		for (long m = x.l(); m <= x.g(); m++) {
			for (long n = y.l(); n <= y.g(); n++) {
				tmp = m ^ n;
				if (tmp > g) {
					g = tmp;
				}
				if (tmp < l) {
					l = tmp;
				}
			}
		}
		return new Interval(l, g);
	}
	
	public static Interval naivAND(Interval x, Interval y) throws IllegalArgumentException {
		long l = x.l() & y.l();
		long g = x.g() & y.g();
		long tmp = 0;
		for (long m = x.l(); m <= x.g(); m++) {
			for (long n = y.l(); n <= y.g(); n++) {
				tmp = m & n;
				if (tmp > g) {
					//System.out.println("Greater: " + m + " " + n + " = " + tmp);
					g = tmp;
				}
				if (tmp < l) {
					//System.out.println("Lesser: " + m + " " + n + " = " + tmp);
					l = tmp;
				}
			}
		}
		return new Interval(l, g);
	}
	
	private static long max(long a, long b) {
		if (a > b) {
			return a;
		}
		return b;
	}
	
	private static long min(long a, long b) {
		if (a > b) {
			return b;
		}
		return a;
	}
	
	private static long UNSAVE_LOWER_XOR(	long a, long b,
			long c, long d) {
		long m, temp;
		m = Long.MIN_VALUE;
		
		while (m != 0) {
			if ((~a & c & m) != 0) {
				temp = (a | m) & -m;
				/*System.out.println("a = " + Long.toBinaryString(a));
				System.out.println("m = " + Long.toBinaryString(m));
				System.out.println("- = " + Long.toBinaryString(-m));
				System.out.println();*/
				if ((temp <= b) && (temp >= a)) {
					a = temp;
					//System.out.println("temp = " + temp);
				}
			}
			else if ((a & ~c & m) != 0) {
				temp = (c | m) & -m;
				if ((temp <= d) && (temp >= c)) {
					//System.out.println("c = 0; tmp " + temp + " c" + c + " d" + d); 
					c = temp;
				}
			}
			m = m >>> 1;
			/*try {
			Thread.currentThread().sleep(100);
			} catch (InterruptedException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
			}*/
			//System.out.println(m);
		}
		//System.out.println(a + " " + c);
		return a ^ c;
	}
	
	private static long UNSAVE_UPPER_XOR(	long a, long b,
											long c, long d) {
		long tmp = 0;
		long m = Long.MIN_VALUE;
		
		while (m != 0) {
			if ((b & d & m) != 0) {
				tmp = (b - m) | (m - 1);
				if ((tmp >= a) && (tmp <= b)) {
					b = tmp;
				} else {
					tmp = (d - m) | (m - 1);
					if ((tmp >= c) && (tmp <= d)) {
						d = tmp;
					}
				}
			}
			m = m >>> 1;
		}
		return b ^ d;
	}
	
	/**
	 * 
	 * @param a
	 * @param b
	 * @param c
	 * @param d
	 * @return
	 */
	private static long UNSAVE_LOWER_AND (	long a, long b,
											long c, long d) {
		long m, temp;
		m = Long.MIN_VALUE;
		
		while (m != 0) {
			if ((~a & ~c & m) != 0) {
				temp = (a | m) & -m;
				//System.out.println("TempA " + temp);
				if ((temp <= b) && (temp >= a)) {
					a = temp;
					break;
				}
				temp = (c | m) & -m;
				//System.out.println("TempC " + temp);
				if ((temp <= d) && (temp >= c)) {
					c = temp;
					break;
				}
			}
			m = m >>> 1;
		}
		return a & c;
	}
	
	/**
	 * 
	 * @param a
	 * @param b
	 * @param c
	 * @param d
	 * @return
	 */
	private static long UNSAVE_UPPER_AND( 	long a, long b,
											long c, long d) {
		long m, temp;
		m = Long.MIN_VALUE;
		
		while (m != 0) {
			if ((b & ~d & m) != 0) {
				temp = (b & ~m) | (m - 1);
				if ((temp >= a) && (temp <= b)) {
					//System.out.println("set b to " + b);
					b = temp;
					break;
				}
			} else if ((~b & d & m) != 0) {
				temp = (d & ~m) | (m - 1);
				if ((temp >= c) && (temp <= d)) { //>= | >
					//System.out.println("set d to" + temp);
					d = temp;
					break;
				}
			}
			m = m >>> 1;
		}
		//System.out.println(b + " " + d);
		return b & d;
	}
	
	private static long UNSAVE_LOWER_OR ( 	long a, long b,
											long c, long d) {
		long m, temp;
		m = Long.MIN_VALUE;
		//System.out.println(a + " " + b + " "+ c + " "+ d);
		while (m != 0) {
			if ((~a & c & m) != 0) {
				temp = (a | m) & -m;
				if ((temp <= b) && (temp >= a)){
					//System.out.println("temp ANOT " + temp);
					a = temp; break;
				}
			}
			else if ((a & ~c & m) != 0) {
				temp = (c | m) & -m;
				//System.out.println(temp);
				if ((temp <= d) && temp >= c) {
					//System.out.println("temp CNOT " + temp);
					c = temp; break;
				}
			}
			m = m >>> 1;
		}
		//System.out.println("a = " + a + " b = " + b);
		return a | c;
	}
			
	private static long UNSAVE_UPPER_OR(long a, long b, 
										long c, long d) {
		long m, temp;
		m = Long.MIN_VALUE;
		
		//printf("compute intervall [%d..%d] maxOR [%d..%d]\n", a, b, c, d);
		
		while (m != 0) {
			if ((b & d & m) != 0) {
				//printf("in case!\n");
				temp = (b - m) | (m - 1);
				if ((temp >= a) && (temp <= b)) {
					b = temp; break;
				}
				temp = (d - m) | (m - 1);
				if ((temp >= c) && (temp <= d)) {
					d = temp; break;
				}
			}
			m = m >>> 1;
		}
		return b | d;
	}
}
