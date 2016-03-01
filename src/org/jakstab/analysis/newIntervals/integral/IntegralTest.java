package org.jakstab.analysis.newIntervals.integral;

import org.jakstab.analysis.newIntervals.Bits;

import java.math.BigInteger;
import java.util.Random;

/**
 * Created by jonas on 2/29/16.
 */
public class IntegralTest {
	public static void main(String[] args) {
		long[] testData = new long[] {-5, -4, -3, -2, -1, 0, 1, 2, 3, 4, 5};
		Bits[] bits = new Bits[] {Bits.BIT8, Bits.BIT16, Bits.BIT32, Bits.BIT64};
		System.out.println("Running integral test...");
		for (Bits bit : bits) {
			for (long a : testData) {
				for (long b : testData) {
					test(a, b, bit);
				}
			}
			Random r = new Random();
			for (int i = 0; i < 1000; i++) {
				test(r.nextLong(), r.nextLong(), bit);
			}
		}
		System.out.println("Done");
		assert false;
	}

	private static void test(long a, long b, Bits bit) {
		a = a & bit.getMask();
		b = b & bit.getMask();
		Word ao = Word.mkWord(a, bit);
		Word bo = Word.mkWord(b, bit);
		BigInteger ba = BigInteger.valueOf(a & 0xFFFFFFFFL).or(BigInteger.valueOf(a >>> 32).shiftLeft(32));
		BigInteger bb = BigInteger.valueOf(b & 0xFFFFFFFFL).or(BigInteger.valueOf(b >>> 32).shiftLeft(32));
		ok(ba.compareTo(BigInteger.ZERO) >= 0, "Created negative literal: " + a);
		ok(bb.compareTo(BigInteger.ZERO) >= 0, "Created negative literal: " + b);
		ok(ba.add(bb), ao.add(bo), a + " + " + b);
		ok(ba.subtract(bb), ao.sub(bo), a + " - " + b);
		ok(ba.multiply(bb), ao.mul(bo), a + " * " + b);
		if (b != 0) {
			ok(ba.divide(bb), ao.div(bo), a + " / " + b);
			ok(ba.mod(bb), ao.mod(bo), a + " % " + b);
		}
		ok(ba.add(BigInteger.ONE), ao.inc(), a + "++");
		ok(bb.add(BigInteger.ONE), bo.inc(), b + "++");
		ok(ba.subtract(BigInteger.ONE), ao.dec(), a + "--");
		ok(bb.subtract(BigInteger.ONE), bo.dec(), b + "--");

		long c = b & (bit.getBits() - 1);
		BigInteger cb = BigInteger.valueOf(c);
		Word co = Word.mkWord(c, bit);
		ok(ba.shiftLeft(cb.intValue()), ao.shl(co), a + " << " + c);
		ok(ba.shiftRight(cb.intValue()), ao.shr(co), a + " >>> " + c);
		ok(ba.and(bb), ao.and(bo), a + " & " + b);
		ok(ba.or(bb), ao.or(bo), a + " | " + b);
		ok(ba.xor(bb), ao.xor(bo), a + " ^ " + b);
		ok(ba.not(), ao.not(), "~" + a);
		ok(bb.not(), bo.not(), "~" + b);

		ok((ba.compareTo(bb) == ao.compareTo(bo)), a + " cmp " + b);
		ok((ba.compareTo(bb) == -1) == ao.lessThan(bo), a + " < " + b);
		ok((ba.compareTo(bb) == 1) == ao.greaterThan(bo), a + " > " + b);
		ok((ba.compareTo(bb) != 1) == ao.lessThanOrEqual(bo), a + " <= " + b);
		ok((ba.compareTo(bb) != -1) == ao.greaterThanOrEqual(bo), a + " >= " + b);
		ok((ba.compareTo(bb) == 0) == ao.equalTo(bo), a + " == " + b);
		ok((ba.compareTo(bb) != 0) == ao.unequalTo(bo), a + " != " + b);
	}

	private static void ok(boolean bool, String msg) {
		if (!bool) {
			throw new AssertionError("Assertion failed: " + msg);
		}
	}

	private static void ok(BigInteger a, Word b, String msg) {
		ok(b.mkThis(a.longValue()).equals(b), msg + " --> " + a + " != " + b);
	}
}
