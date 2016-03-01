package org.jakstab.analysis.newIntervals.integral;

import org.jakstab.analysis.newIntervals.Bits;

import java.math.BigInteger;

/**
 * Created by jonas on 2/29/16.
 */
public abstract class Word<T extends Word> implements Integral<T>, Comparable<T> {

	/**
	 * The given internal payload. Upper bits should be 0.
	 */
	protected final long val;

	protected Word(long val) {
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
	protected abstract T mkThis(long val);

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

	public boolean msb() {
		return longValue() < 0;
	}

	@Override
	public T add(T b) {
		return mkThis(val + b.val);
	}

	@Override
	public T sub(T b) {
		return mkThis(val - b.val);
	}

	@Override
	public T mul(T b) {
		return mkThis(val * b.val);
	}

	@Override
	public T div(T b) {
		return mkThis(val / b.val);
	}

	@Override
	public T mod(T b) {
		return mkThis(val % b.val);
	}

	@Override
	public T inc() {
		return mkThis(val + 1);
	}

	@Override
	public T dec() {
		return mkThis(val - 1);
	}

	@Override
	public T shl(T b) {
		if ((b.val & ~63) != 0) {
			return mkThis(0);
		}
		return mkThis(val << b.val);
	}

	@Override
	public T shr(T b) {
		if ((b.val & ~63) != 0) {
			return mkThis(0);
		}
		return mkThis(val >>> b.val);
	}

	@Override
	public T and(T b) {
		return mkThis(val & b.val);
	}

	@Override
	public T or(T b) {
		return mkThis(val | b.val);
	}

	@Override
	public T xor(T b) {
		return mkThis(val ^ b.val);
	}

	@Override
	public T not() {
		return mkThis(~val);
	}

	@Override
	public boolean lessThan(T b) {
		return val < b.val;
	}

	@Override
	public boolean greaterThan(T b) {
		return !lessThanOrEqual(b);
	}

	@Override
	public boolean lessThanOrEqual(T b) {
		return val <= b.val;
	}

	@Override
	public boolean greaterThanOrEqual(T b) {
		return !lessThan(b);
	}

	@Override
	public boolean equalTo(T b) {
		return val == b.val;
	}

	@Override
	public boolean unequalTo(T b) {
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
	public int compareTo(T o) {
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
	public static Word<?> mkWord(Word w, Bits bits) {
		if ((w.val & bits.getMask()) == w.val) {
			return w;
		}
		return mkWord(w.val, bits);
	}
}
