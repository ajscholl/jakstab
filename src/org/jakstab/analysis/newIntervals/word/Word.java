package org.jakstab.analysis.newIntervals.word;

import org.jakstab.analysis.newIntervals.Bits;

import java.math.BigInteger;
import java.util.Map;

public abstract class Word implements Comparable<Word> {

	/**
	 * The given internal payload. Upper bits should be 0.
	 */
	protected final long val;

	protected Word(long val) {
		assert getMask() != -1L || this instanceof Word64;
		this.val = val & getMask();
	}

	/**
	 * Mask leaving only the relevant bits set.
	 *
	 * @return The mask.
	 */
	public abstract long getMask();

	/**
	 * Create a new instance of me, but with the given payload.
	 *
	 * @param val The payload.
	 * @return The new instance.
	 */
	protected abstract Word mkThis(long val);

	/**
	 * Get the cache for this type.
	 *
	 * @return The cache.
	 */
	protected abstract Map<Long, Word> getCache();

	/**
	 * Create a new instance of me, but with the given payload. Caches small numbers to reduce memory pressure.
	 *
	 * @param val The payload.
	 * @return The new instance.
	 */
	protected Word mkThisCached(long val) {
		if (val <= 0xFFL && val >= -0xFFL) {
			Map<Long, Word> cache = getCache();
			Long keyVal = val;
			Word w = cache.get(keyVal);
			if (w == null) {
				w = mkThis(val);
				cache.put(keyVal, w);
			}
			return w;
		}
		return mkThis(val);
	}

	/**
	 * Get the internal representation of the number. The upper bits may be zero even
	 * when the they should be sign extended. You may want to consider using longValue instead.
	 *
	 * @return The internal value.
	 */
	public long unsafeInternalValue() {
		return val;
	}

	/**
	 * Get the sign extended number as a long.
	 *
	 * @return A long with the same value as the stored value.
	 */
	public abstract long longValue();

	/**
	 * Return the value as a big integer.
	 *
	 * @return The value as a big integer.
	 */
	public BigInteger bigValue() {
		return BigInteger.valueOf(unsafeInternalValue());
	}

	/**
	 * Return the most significant bit.
	 *
	 * @return The most significant bit.
	 */
	public boolean msb() {
		return longValue() < 0L;
	}

	/**
	 * Return the sign of a word. 0 has a positive sign.
	 *
	 * @return The sign of a word.
	 */
	public Word sign() {
		return mkThisCached(msb() ? -1L : 1L);
	}

	public Word add(Word b) {
		return mkThisCached(val + b.val);
	}

	public Word sub(Word b) {
		return mkThisCached(val - b.val);
	}

	public Word mul(Word b) {
		return mkThisCached(val * b.val);
	}

	public Word udiv(Word b) {
		return mkThisCached(val / b.val);
	}

	public Word sdiv(Word b) {
		return mkThisCached(longValue() / b.longValue());
	}

	public Word umod(Word b) {
		return mkThisCached(val % b.val);
	}

	public Word smod(Word b) {
		return mkThisCached(longValue() % b.longValue());
	}

	public Word inc() {
		return mkThisCached(val + 1L);
	}

	public Word dec() {
		return mkThisCached(val - 1L);
	}

	public Word negate() {
		return not().inc();
	}

	public Word shl(int b) {
		if ((b & ~63) != 0) {
			return mkThisCached(0L);
		}
		return mkThisCached(val << (long)b);
	}

	public Word shr(int b) {
		if ((b & ~63) != 0) {
			return mkThis(0L);
		}
		return mkThisCached(val >>> (long)b);
	}

	public Word and(Word b) {
		return mkThisCached(val & b.val);
	}

	public Word or(Word b) {
		return mkThisCached(val | b.val);
	}

	public Word xor(Word b) {
		return mkThisCached(val ^ b.val);
	}

	public Word not() {
		return mkThisCached(~val);
	}

	public boolean lessThan(Word b) {
		return val < b.val;
	}

	public boolean greaterThan(Word b) {
		return !lessThanOrEqual(b);
	}

	public boolean lessThanOrEqual(Word b) {
		return val <= b.val;
	}

	public boolean greaterThanOrEqual(Word b) {
		return !lessThan(b);
	}

	public boolean equalTo(Word b) {
		return val == b.val;
	}

	public boolean unequalTo(Word b) {
		return val != b.val;
	}

	@Override
	public boolean equals(Object obj) {
		return obj != null && obj instanceof Word && ((Word)obj).val == val;
	}

	@Override
	public int hashCode() {
		return (int)val ^ (int)(val >>> 32);
	}

	@Override
	public String toString() {
		return Long.toString(val);
	}

	@Override
	public int compareTo(Word o) {
		if (lessThan(o)) {
			return -1;
		}
		if (val == o.val) {
			return 0;
		}
		return 1;
	}

	/**
	 * Create a new word of the given size.
	 *
	 * @param w The payload.
	 * @param bits The size.
	 * @return The word.
	 */
	public static Word mkWord(long w, Bits bits) {
		switch (bits) {
			case BIT1: return new Word1(w);
			case BIT8: return new Word8(w);
			case BIT16: return new Word16(w);
			case BIT32: return new Word32(w);
			case BIT64: return new Word64(w);
			default: throw new IllegalArgumentException("Unknown bitsize: " + bits);
		}
	}

	/**
	 * Create a new word of the given size.
	 *
	 * @param w The payload.
	 * @param bits The size.
	 * @return The word.
	 */
	public static Word mkWord(Word w, Bits bits) {
		if ((w.val & bits.getMask()) == w.val) {
			return w;
		}
		return mkWord(w.val, bits);
	}
}
