package org.jakstab.analysis.newIntervals.word;

import java.math.BigInteger;
import java.util.HashMap;

public class Word64 extends Word {

	private static HashMap<Long, Word> cache = new HashMap<>();

	public Word64(long val) {
		super(val, ~0L);
	}

	@Override
	public Word mkThis(long val) {
		return new Word64(val);
	}

	@Override
	public long longValue() {
		return val;
	}

	@Override
	protected HashMap<Long, Word> getCache() {
		return cache;
	}

	@Override
	public BigInteger bigValue() {
		return wordToBigInteger(val);
	}

	@Override
	public Word mul(Word b) {
		return valueOf(bigValue().multiply(b.bigValue()).longValue());
	}

	@Override
	public Word udiv(Word b) {
		return valueOf(bigValue().divide(b.bigValue()).longValue());
	}

	@Override
	public Word umod(Word b) {
		return valueOf(bigValue().mod(b.bigValue()).longValue());
	}

	public static BigInteger wordToBigInteger(long w) {
		if (w < 0L) {
			return BigInteger.valueOf(w).add(BigInteger.valueOf(2L).pow(64));
		}
		return BigInteger.valueOf(w);
	}

	@Override
	public java.lang.String toString() {
		if (val < 0L) {
			return bigValue().toString();
		} else {
			return super.toString();
		}
	}

	@Override
	public boolean lessThan(Word b) {
		if (val < 0L) {
			return b.val < 0L && val < b.val;
		} else {
			return b.val < 0L || val < b.val;
		}
	}

	@Override
	public boolean lessThanOrEqual(Word b) {
		return val == b.val || lessThan(b);
	}
}
