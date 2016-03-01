package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.newIntervals.integral.Word;
import org.jakstab.rtl.BitVectorType;

/**
 * Different data types for different bit sizes.
 */
public enum Bits implements BitVectorType {
	BIT0(-1), BIT1(1), BIT8(8), BIT16(16), BIT32(32), BIT64(64);

	private final int bits;
	private final long mask;

	Bits(int bits) {
		this.bits = bits;
		if (bits == 64) {
			mask = ~0; // all bits set
		} else {
			mask = (1L << (long)bits) - 1L; // 2^bits - 1
		}
	}

	/**
	 * Get the number of bits of this data type. May not be called on an unknwon bit type.
	 * @return bits.
	 */
	public int getBits() {
		assert bits != -1;
		return bits;
	}

	@Override
	public int getBitWidth() {
		return bits;
	}

	/**
	 * Get the mask to shrink a value to this data type.
	 * @return 2^bits - 1.
	 */
	public long getMask() {
		return mask;
	}

	/**
	 * Compute b <=_a c, i.e. compare two numbers relative to some other number.
	 * @param a The number to be relative to.
	 * @param b The first number to compare.
	 * @param c The second number to compare.
	 * @return boolean
	 */
	public static boolean leq(Word a, Word b, Word c) {
		return b.sub(a).lessThanOrEqual(c.sub(a));
	}

	public static Bits fromInt(int bitWidth) {
		switch (bitWidth) {
			case 1: return BIT1;
			case 8: return BIT8;
			case 16: return BIT16;
			case 32: return BIT32;
			case 64: return BIT64;
			default: throw new IllegalArgumentException("Unknown bit-width: " + bitWidth);
		}
	}
}