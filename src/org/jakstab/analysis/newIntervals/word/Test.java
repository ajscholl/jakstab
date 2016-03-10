package org.jakstab.analysis.newIntervals.word;

import org.jakstab.analysis.newIntervals.Bits;

import java.math.BigInteger;
import java.util.Random;

public class Test {
	public static void main(String[] args) {
		System.out.println("Running integral test...");
		Bits[] bits = {Bits.BIT8, Bits.BIT16, Bits.BIT32, Bits.BIT64};
		long[] testData = {-5L, -4L, -3L, -2L, -1L, 0L, 1L, 2L, 3L, 4L, 5L};
		for (Bits bit : bits) {
			for (long a : testData) {
				for (long b : testData) {
					test(a, b, bit);
				}
			}
			Random r = new Random();
			for (int i = 0; i < 100000; i++) {
				test(r.nextLong(), r.nextLong(), bit);
			}
		}
		System.out.println("Done");
	}

	private static void test(long a, long b, Bits bit) {
		long la = a & bit.getMask();
		long lb = b & bit.getMask();
		Word ao = Word.mkWord(la, bit);
		Word bo = Word.mkWord(lb, bit);
		ok(la == (ao.longValue() & bit.getMask()), "longValue failed for " + a + " (" + bit + ')');
		ok(lb == (bo.longValue() & bit.getMask()), "longValue failed for " + b + " (" + bit + ')');
		a = ao.longValue();
		b = bo.longValue();
		BigInteger ba = BigInteger.valueOf(la & 0xFFFFFFFFL).or(BigInteger.valueOf(la >>> 32).shiftLeft(32));
		BigInteger bb = BigInteger.valueOf(lb & 0xFFFFFFFFL).or(BigInteger.valueOf(lb >>> 32).shiftLeft(32));
		ok(ba.compareTo(BigInteger.ZERO) >= 0, "Created negative literal: " + la);
		ok(bb.compareTo(BigInteger.ZERO) >= 0, "Created negative literal: " + lb);
		ok(ba.add(bb), ao.add(bo), la + " + " + lb);
		ok(ba.subtract(bb), ao.sub(bo), la + " - " + lb);
		ok(ba.multiply(bb), ao.mul(bo), la + " * " + lb);
		if (lb != 0L) {
			ok(ba.divide(bb), ao.udiv(bo), la + " /u " + lb);
			ok(BigInteger.valueOf(a / b), ao.sdiv(bo), la + " /s " + lb);
			ok(ba.mod(bb), ao.umod(bo), la + " %u " + lb);
			ok(BigInteger.valueOf(a % b), ao.smod(bo), la + " %s " + lb);
		}
		ok(ba.add(BigInteger.ONE), ao.inc(), la + "++");
		ok(bb.add(BigInteger.ONE), bo.inc(), lb + "++");
		ok(ba.subtract(BigInteger.ONE), ao.dec(), la + "--");
		ok(bb.subtract(BigInteger.ONE), bo.dec(), lb + "--");

		long c = lb & (long) bit.getBits() - 1L;
		BigInteger cb = BigInteger.valueOf(c);
		ok(ba.shiftLeft(cb.intValue()), ao.shl((int)c), la + " << " + c);
		ok(ba.shiftRight(cb.intValue()), ao.shr((int)c), la + " >>> " + c);
		ok(ba.and(bb), ao.and(bo), la + " & " + lb);
		ok(ba.or(bb), ao.or(bo), la + " | " + lb);
		ok(ba.xor(bb), ao.xor(bo), la + " ^ " + lb);
		ok(ba.not(), ao.not(), "~" + la);
		ok(bb.not(), bo.not(), "~" + lb);

		ok(ba.compareTo(bb) == ao.compareTo(bo), la + " cmp " + lb);
		ok((ba.compareTo(bb) == -1) == ao.lessThan(bo), la + " < " + lb);
		ok((ba.compareTo(bb) == 1) == ao.greaterThan(bo), la + " > " + lb);
		ok((ba.compareTo(bb) != 1) == ao.lessThanOrEqual(bo), la + " <= " + lb);
		ok((ba.compareTo(bb) != -1) == ao.greaterThanOrEqual(bo), la + " >= " + lb);
		ok((ba.compareTo(bb) == 0) == ao.equalTo(bo), la + " == " + lb);
		ok((ba.compareTo(bb) != 0) == ao.unequalTo(bo), la + " != " + lb);
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
