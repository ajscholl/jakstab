package org.jakstab.analysis.newIntervals.integral;

import java.math.BigInteger;

public class Word64 extends Word<Word64> implements Integral<Word64> {

	public Word64(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return ~0;
	}

	@Override
	public Word64 mkThis(long val) {
		return new Word64(val);
	}

	@Override
	public long longValue() {
		return val;
	}

	@Override
	public BigInteger bigValue() {
		return wordToBigInteger(val);
	}

	@Override
	public Word64 mul(Word64 b) {
		return mkThis(bigValue().multiply(b.bigValue()).longValue());
	}

	@Override
	public Word64 div(Word64 b) {
		return mkThis(bigValue().divide(b.bigValue()).longValue());
	}

	@Override
	public Word64 mod(Word64 b) {
		return mkThis(bigValue().mod(b.bigValue()).longValue());
	}

	public static BigInteger wordToBigInteger(long w) {
		if (w < 0) {
			return BigInteger.valueOf(w).add(BigInteger.valueOf(2).pow(64));
		}
		return BigInteger.valueOf(w);
	}

	@Override
	public String toString() {
		if (val < 0) {
			return bigValue().toString();
		} else {
			return super.toString();
		}
	}

	@Override
	public boolean lessThan(Word64 b) {
		if (val < 0) {
			return b.val < 0 && val < b.val;
		} else {
			return b.val < 0 || val < b.val;
		}
	}

	@Override
	public boolean lessThanOrEqual(Word64 b) {
		return val == b.val || lessThan(b);
	}
}
