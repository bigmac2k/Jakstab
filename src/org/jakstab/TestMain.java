package org.jakstab;

import org.jakstab.analysis.intervals.util.BitwiseOperations;
import org.jakstab.analysis.intervals.util.Interval;

import java.util.Random;

public class TestMain {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
		testBitNegate(10, 50);
	}

	public static void testBitNegate(int cases, int bound) {
		long seed = System.currentTimeMillis() % 1000;
		
		Random rnd = new Random(seed);
		
		Interval res1, res2, x, y;
		long a, b;
		long swap;
		
		res1 = BitwiseOperations.BIT_NEGATE(0, 0);
		res2 = BitwiseOperations.naivBitNeg(0, 0);
		
		if (!res1.equals(res2)) {
			System.out.println("Case (00): " + cases + " mismatch! \t" + res1 + "\t" + res2);
		}
		
		while (cases > 0) {
			// rnd can return negative values
			b = Math.abs(rnd.nextInt() % bound);
			if (b == 0) {
				a = 0;
			} else {
				a = Math.abs(rnd.nextLong() % b);
			}
			
			//System.out.println(a +" "+ b);
			res1 = BitwiseOperations.BIT_NEGATE(a, b);
			//System.out.println("got res 1");
			res2 = BitwiseOperations.naivBitNeg(a, b);
			//System.out.println("got res 2");
			
			if (!res1.equals(res2)) {
				System.out.println("Case (++): " + cases + " mismatch! \t" + res1 + "\t" + res2);
			}
			
			a *= -1;
			//System.out.println(a +" "+ b);
			res1 = BitwiseOperations.BIT_NEGATE(a, b);
			res2 = BitwiseOperations.naivBitNeg(a, b);
			
			if (!res1.equals(res2)) {
				System.out.println("Case (-+): " + cases + " mismatch! \t" + res1 + "\t" + res2);
			}
			
			swap = a;
			a = 0;
			//System.out.println(a +" "+ b);
			res1 = BitwiseOperations.BIT_NEGATE(a, b);
			res2 = BitwiseOperations.naivBitNeg(a, b);
			
			if (!res1.equals(res2)) {
				System.out.println("Case (0+): " + cases + " mismatch! \t" + res1 + "\t" + res2);
			}
			
			a = swap;
			swap = b;
			b = 0;
			//System.out.println(a +" "+ b);
			res1 = BitwiseOperations.BIT_NEGATE(a, b);
			res2 = BitwiseOperations.naivBitNeg(a, b);
			
			if (!res1.equals(res2)) {
				System.out.println("Case (-0): " + cases + " mismatch! \t" + res1 + "\t" + res2);
			}
			
			b = a;
			a = -1 * swap;
			//System.out.println(a +" "+ b);
			res1 = BitwiseOperations.BIT_NEGATE(a, b);
			res2 = BitwiseOperations.naivBitNeg(a, b);
			
			if (!res1.equals(res2)) {
				System.out.println("Case (--): " + cases + " mismatch! \t" + res1 + "\t" + res2);
			}
			cases--;
		}
		System.out.println("Test cases completed");
	}
}
