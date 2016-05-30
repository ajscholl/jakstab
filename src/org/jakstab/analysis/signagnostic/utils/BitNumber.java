package org.jakstab.analysis.signagnostic.utils;

import org.jakstab.analysis.signagnostic.statistic.Statistic;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.Optional;

import java.lang.ref.WeakReference;
import java.math.BigInteger;
import java.util.Map;
import java.util.WeakHashMap;

/**
 * Integer type with variable bit width between 1 and 64. Compares using unsigned interpretation of the bit patterns, but
 * operations to operate on signed interpretations of the bit patterns exist, too.
 *
 * @author A. J. Scholl
 */
public class BitNumber implements Comparable<BitNumber>, BitVectorType {

	/**
	 * The given internal payload.
	 */
	private final long val;

	/**
	 * The size of this integer in bits.
	 */
	private final int bitSize;

	/**
	 * The mask for this value.
	 */
	private final long mask;

	/**
	 * 2^64.
	 */
	private static final BigInteger POW_2_64 = BigInteger.valueOf(2L).pow(64);

	/**
	 * Cache from DynIntegers to weak references of them. The weak hash map does not keep the
	 * keys alive, so if the key keeps on living and the value (which is the same as the key)
	 * does too, one can reuse the value in the map.
	 */
	private static final Map<BitNumber, WeakReference<BitNumber>> cache = new WeakHashMap<>();

	public static final BitNumber TRUE = new BitNumber(1, 1);
	public static final BitNumber FALSE = new BitNumber(0, 1);

	static {
		cache.put(TRUE, new WeakReference<>(TRUE));
		cache.put(FALSE, new WeakReference<>(FALSE));
	}

	/**
	 * Create a new {@link BitNumber} with the given payload and bitsize.
	 *
	 * @param val Payload.
	 * @param bitSize Bitsize.
	 */
	public BitNumber(int val, int bitSize) {
		this((long)val & 0xFFFFFFFFL, bitSize);
	}

	/**
	 * Create a new {@link BitNumber} with the given payload and bitsize.
	 *
	 * @param val Payload.
	 * @param bitSize Bitsize.
	 */
	public BitNumber(long val, int bitSize) {
		assert bitSize >= 1 && bitSize <= 64 : "bit-size too small or large";
		mask = bit(bitSize) - 1L;
		assert mask != 0L;
		this.val = val & mask;
		this.bitSize = bitSize;
		Statistic.countBitNumberCreate();
	}

	private void assertCompatible(BitNumber b) {
		assert bitSize == b.bitSize : "Incompatible bit sizes in " + this + " and " + b;
	}

	/**
	 * Get the zero extended number as a long. Note that 64 bit numbers still return negative results.
	 *
	 * @return A long with the same value as the stored value.
	 */
	public long zExtLongValue() {
		assert bitSize == 64 || val >= 0L;
		return val;
	}

	/**
	 * Get the sign extended number as a long.
	 *
	 * @return A long with the same value as the stored value.
	 */
	public long sExtLongValue() {
		if (msb()) {
			return ~mask | val;
		}
		return val;
	}

	/**
	 * Return the signed value as a big integer.
	 *
	 * @return The signed value as a big integer.
	 */
	public BigInteger signedBigValue() {
		return BigInteger.valueOf(sExtLongValue());
	}

	/**
	 * Return the unsigned value as a big integer.
	 *
	 * @return The unsigned value as a big integer.
	 */
	public BigInteger unsignedBigValue() {
		if (val < 0L) {
			assert bitSize == 64;
			return BigInteger.valueOf(val).add(POW_2_64);
		}
		return BigInteger.valueOf(val);
	}

	/**
	 * Return the most significant bit.
	 *
	 * @return The most significant bit.
	 */
	public boolean msb() {
		long m = bit(bitSize - 1);
		return (val & m) != 0L;
	}

	/**
	 * Return the sign of a word. 0 has a positive sign.
	 *
	 * @return The sign of a word.
	 */
	public BitNumber sign() {
		return valueOf(msb() ? -1L : 1L);
	}

	/**
	 * Add two numbers.
	 *
	 * @param b The other number.
	 * @return Result of the addition.
	 */
	public BitNumber add(BitNumber b) {
		assertCompatible(b);
		return valueOf(val + b.val);
	}


	/**
	 * Subtract one number from this number.
	 *
	 * @param b The other number.
	 * @return Result of the subtraction.
	 */
	public BitNumber sub(BitNumber b) {
		assertCompatible(b);
		return valueOf(val - b.val);
	}

	/**
	 * Multiply two numbers.
	 *
	 * @param b The other number.
	 * @return Result of the multiplication.
	 */
	public BitNumber mul(BitNumber b) {
		assertCompatible(b);
		return valueOf(val * b.val);
	}

	/**
	 * Check if signed multiplication would overflow.
	 *
	 * @param b The other number.
	 * @return True if multiplication would overflow.
	 */
	public boolean sMulOverflow(BitNumber b) {
		assertCompatible(b);
		if (bitSize <= 32) {
			assert (val & 0xFFFFFFFF00000000L) == 0L;
			assert (b.val & 0xFFFFFFFF00000000L) == 0L;
			long r = val * b.val;
			return (r & 0xFFFFFFFF00000000L) != 0L;
		} else {
			return !signedBigValue().multiply(b.signedBigValue()).equals(BigInteger.valueOf(val * b.val));
		}
	}

	/**
	 * Check if unsigned multiplication would overflow.
	 *
	 * @param b The other number.
	 * @return True if multiplication would overflow.
	 */
	public boolean uMulOverflow(BitNumber b) {
		assertCompatible(b);
		if (bitSize <= 32) {
			assert (val & 0xFFFFFFFF00000000L) == 0L;
			assert (b.val & 0xFFFFFFFF00000000L) == 0L;
			long r = val * b.val;
			return (r & 0xFFFFFFFF00000000L) != 0L;
		} else {
			return !unsignedBigValue().multiply(b.unsignedBigValue()).equals(BigInteger.valueOf(val * b.val));
		}
	}

	/**
	 * Unsigned quotient two numbers.
	 *
	 * @param b The other number.
	 * @return Result of the division.
	 */
	public BitNumber uquot(BitNumber b) {
		assertCompatible(b);
		if (b.val == 0L) {
			throw new ArithmeticException("Unsigned division of " + this + " by zero");
		}
		if (bitSize < 64) {
			return valueOf(zExtLongValue() / b.zExtLongValue());
		}
		return valueOf(unsignedBigValue().divide(b.unsignedBigValue()).longValue());
	}

	/**
	 * Signed quotient two numbers.
	 *
	 * @param b The other number.
	 * @return Result of the division.
	 */
	public BitNumber squot(BitNumber b) {
		assertCompatible(b);
		if (b.val == 0L) {
			throw new ArithmeticException("Signed division of " + this + " by zero");
		} else if (b.sExtLongValue() == -1L && equals(sMinVal())) {
			throw new ArithmeticException("Overflow in signed division of " + this + " and -1");
		}
		return valueOf(sExtLongValue() / b.sExtLongValue());
	}

	/**
	 * Unsigned remainder two numbers.
	 *
	 * @param b The other number.
	 * @return Remainder.
	 */
	public BitNumber urem(BitNumber b) {
		assertCompatible(b);
		if (b.val == 0L) {
			throw new ArithmeticException("Unsigned remainder of " + this + " and zero");
		}
		if (bitSize < 64) {
			return valueOf(zExtLongValue() % b.zExtLongValue());
		}
		return valueOf(unsignedBigValue().mod(b.unsignedBigValue()).longValue());
	}

	/**
	 * Signed remainder two numbers.
	 *
	 * @param b The other number.
	 * @return Remainder.
	 */
	public BitNumber srem(BitNumber b) {
		assertCompatible(b);
		if (b.val == 0L) {
			throw new ArithmeticException("Signed remainder of " + this + " and zero");
		} else if (b.sExtLongValue() == -1L && equals(sMinVal())) {
			throw new ArithmeticException("Overflow in signed remainder of " + this + " and -1");
		}
		return valueOf(sExtLongValue() % b.sExtLongValue());
	}

	/**
	 * GCD two numbers.
	 *
	 * @param b The other number.
	 * @return GCD.
	 */
	public BitNumber gcd(BitNumber b) {
		assertCompatible(b);
		return valueOf(unsignedBigValue().gcd(b.unsignedBigValue()).longValue());
	}

	/**
	 * LCM two numbers. Returns nothing if overflow happens
	 *
	 * @param b The other number.
	 * @return LCM.
	 */
	public Optional<BitNumber> lcm(BitNumber b) {
		assertCompatible(b);
		BigInteger tmp = lcm(unsignedBigValue(), b.unsignedBigValue());
		BitNumber result = valueOf(tmp.longValue());
		if (result.unsignedBigValue().equals(tmp)) {
			return new Optional<>(result);
		} else {
			// Overflow in lcm
			return Optional.none();
		}
	}

	/**
	 * LCM of two BigIntegers.
	 *
	 * @param a First number.
	 * @param b Second number.
	 * @return LCM.
	 */
	private static BigInteger lcm(BigInteger a, BigInteger b) {
		if (a.equals(BigInteger.ZERO) || b.equals(BigInteger.ZERO)) {
			return BigInteger.ZERO;
		} else {
			return a.divide(a.gcd(b)).multiply(b).abs();
		}
	}

	/**
	 * Compute a|b, i.e. whether c exists such that b = ac.
	 *
	 * @param b b
	 * @return a|b.
	 */
	public boolean dividedBy(BitNumber b) {
		assertCompatible(b);
		return zExtLongValue() == 0L || b.urem(this).sExtLongValue() == 0L;
	}

	/**
	 * Increment this number.
	 *
	 * @return This + 1.
	 */
	public BitNumber inc() {
		return valueOf(val + 1L);
	}

	/**
	 * Decrement this number.
	 *
	 * @return This - 1.
	 */
	public BitNumber dec() {
		return valueOf(val - 1L);
	}

	/**
	 * Negate this number.
	 *
	 * @return -This.
	 */
	public BitNumber negate() {
		return valueOf(-val);
	}

	/**
	 * Shift this number to the left. Shifts greater than the bitsize or smaller 0 yield 0.
	 *
	 * @param b The number of bits to shift.
	 * @return This << b.
	 */
	public BitNumber shl(int b) {
		if (b >= bitSize || b < 0) {
			return valueOf(0L);
		}
		return valueOf(val << b);
	}

	/**
	 * Logical shift this number to the right. Shifts greater than the bitsize or smaller 0 yield 0.
	 *
	 * @param b The number of bits to shift.
	 * @return This >>> b.
	 */
	public BitNumber shr(int b) {
		if (b >= bitSize || b < 0) {
			return valueOf(0L);
		}
		return valueOf(val >>> b);
	}

	/**
	 * Arithmetic shift this number to the right. Shifts greater than the bitsize or smaller 0 yield only sign bits.
	 *
	 * @param b The number of bits to shift.
	 * @return This >> b.
	 */
	public BitNumber sar(int b) {
		if (b >= bitSize || b < 0) {
			return valueOf(msb() ? ~0L : 0L);
		}
		return valueOf(val >> b);
	}

	/**
	 * Create a number with the n-th bit set.
	 *
	 * @param n The bit to set.
	 * @return 1 << n.
	 */
	public static long bit(int n) {
		if (n > 0 && (n & 63) == 0) {
			return 0L;
		}
		return 1L << n;
	}

	/**
	 * Bitwise and of two numbers.
	 *
	 * @param b The other number.
	 * @return Bitwise and.
	 */
	public BitNumber and(BitNumber b) {
		assertCompatible(b);
		return valueOf(val & b.val);
	}

	/**
	 * Bitwise or of two numbers.
	 *
	 * @param b The other number.
	 * @return Bitwise or.
	 */
	public BitNumber or(BitNumber b) {
		assertCompatible(b);
		return valueOf(val | b.val);
	}

	/**
	 * Bitwise xor of two numbers.
	 *
	 * @param b The other number.
	 * @return Bitwise xor.
	 */
	public BitNumber xor(BitNumber b) {
		assertCompatible(b);
		return valueOf(val ^ b.val);
	}

	/**
	 * Invert all bits.
	 *
	 * @return The new number.
	 */
	public BitNumber not() {
		return valueOf(~val);
	}

	/**
	 * Return the number of leading zero bits.
	 *
	 * @return The number of leading zero bits.
	 */
	public int numberOfLeadingZeros() {
		return Long.numberOfLeadingZeros(val) - (64 - bitSize);
	}

	/**
	 * Truncate a number to a smaller size.
	 * @param bitSize The smaller size.
	 * @return The truncated number.
	 */
	public BitNumber trunc(int bitSize) {
		assert bitSize <= this.bitSize;
		return valueOf(val, bitSize);
	}

	/**
	 * Zero extend a number to a bigger size.
	 * @param bitSize The bigger size.
	 * @return The zero extended number.
	 */
	public BitNumber zExtend(int bitSize) {
		assert bitSize >= this.bitSize;
		return valueOf(zExtLongValue(), bitSize);
	}

	/**
	 * Sign extend a number to a bigger size.
	 * @param bitSize The bigger size.
	 * @return The sign extended number.
	 */
	public BitNumber sExtend(int bitSize) {
		assert bitSize >= this.bitSize;
		return valueOf(sExtLongValue(), bitSize);
	}

	/**
	 * Unsigned minimum of two values.
	 *
	 * @param b The other value.
	 * @return The minimum.
	 */
	public BitNumber uMin(BitNumber b) {
		return ult(b) ? this : b;
	}

	/**
	 * Unsigned maximum of two values.
	 *
	 * @param b The other value.
	 * @return The maximum.
	 */
	public BitNumber uMax(BitNumber b) {
		return ugt(b) ? this : b;
	}

	/**
	 * Signed minimum of two values.
	 *
	 * @param b The other value.
	 * @return The minimum.
	 */
	public BitNumber sMin(BitNumber b) {
		return slt(b) ? this : b;
	}

	/**
	 * Signed maximum of two values.
	 *
	 * @param b The other value.
	 * @return The maximum.
	 */
	public BitNumber sMax(BitNumber b) {
		return sgt(b) ? this : b;
	}

	/**
	 * Signed less than two numbers.
	 *
	 * @param b The other number.
	 * @return this <_s b.
	 */
	public boolean slt(BitNumber b) {
		assertCompatible(b);
		return sExtLongValue() < b.sExtLongValue();
	}

	/**
	 * Unsigned less than two numbers.
	 *
	 * @param b The other number.
	 * @return this <_u b.
	 */
	public boolean ult(BitNumber b) {
		assertCompatible(b);
		if (bitSize == 64) {
			if (msb()) {
				return b.msb() && val < b.val;
			} else {
				return b.msb() || val < b.val;
			}
		}
		return zExtLongValue() < b.zExtLongValue();
	}

	/**
	 * Signed greater than two numbers.
	 *
	 * @param b The other number.
	 * @return this >_s b.
	 */
	public boolean sgt(BitNumber b) {
		return !sleq(b);
	}

	/**
	 * Unsigned greater than two numbers.
	 *
	 * @param b The other number.
	 * @return this >_u b.
	 */
	public boolean ugt(BitNumber b) {
		return !uleq(b);
	}


	/**
	 * Signed less than or equal two numbers.
	 *
	 * @param b The other number.
	 * @return this <=_u b.
	 */
	public boolean sleq(BitNumber b) {
		return slt(b) || equals(b);
	}


	/**
	 * Unsigned less than or equal two numbers.
	 *
	 * @param b The other number.
	 * @return this >=_u b.
	 */
	public boolean uleq(BitNumber b) {
		return ult(b) || equals(b);
	}


	/**
	 * Signed less than or equal two numbers.
	 *
	 * @param b The other number.
	 * @return this >=_s b.
	 */
	public boolean sgeq(BitNumber b) {
		return !slt(b);
	}


	/**
	 * Unsigned less than or equal two numbers.
	 *
	 * @param b The other number.
	 * @return this >=_u b.
	 */
	public boolean ugeq(BitNumber b) {
		return !ult(b);
	}

	/**
	 * Compare two numbers relative to this number. Comparison is performed
	 * on unsigned numbers after this number was subtracted from both arguments.
	 *
	 * @param b The first number.
	 * @param c The second number.
	 * @return True if b is found before c on the number circle starting from this number.
	 */
	public boolean relativeLeq(BitNumber b, BitNumber c) {
		return b.sub(this).uleq(c.sub(this));
	}

	/**
	 * Return the minimum unsigned value.
	 *
	 * @param bitSize Wanted bitsize of the result.
	 * @return The minimum unsigned value.
	 */
	public static BitNumber uMaxVal(int bitSize) {
		return valueOf(~0L, bitSize);
	}

	/**
	 * Return the maximum unsigned value.
	 *
	 * @param bitSize Wanted bitsize of the result.
	 * @return The maximum unsigned value.
	 */
	public static BitNumber sMaxVal(int bitSize) {
		return valueOf(bit(bitSize - 1) - 1L, bitSize);
	}

	/**
	 * Return the minimum unsigned value.
	 *
	 * @param bitSize Wanted bitsize of the result.
	 * @return The minimum unsigned value.
	 */
	public static BitNumber uMinVal(int bitSize) {
		return valueOf(0L, bitSize);
	}

	/**
	 * Return the minimum signed value.
	 *
	 * @param bitSize Wanted bitsize of the result.
	 * @return The minimum signed value.
	 */
	public static BitNumber sMinVal(int bitSize) {
		return valueOf(bit(bitSize - 1), bitSize);
	}

	/**
	 * Return the maximum unsigned value.
	 *
	 * @return The maximum unsigned value.
	 */
	public BitNumber uMaxVal() {
		return uMaxVal(bitSize);
	}

	/**
	 * Return the maximum signed value.
	 *
	 * @return The maximum signed value.
	 */
	public BitNumber sMaxVal() {
		return sMaxVal(bitSize);
	}

	/**
	 * Return the minimum unsigned value.
	 *
	 * @return The minimum unsigned value.
	 */
	public BitNumber uMinVal() {
		return uMinVal(bitSize);
	}

	/**
	 * Return the minimum signed value.
	 *
	 * @return The minimum signed value.
	 */
	public BitNumber sMinVal() {
		return sMinVal(bitSize);
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof BitNumber) {
			BitNumber b = (BitNumber) obj;
			assert (b.mask == mask) == (b.bitSize == bitSize);
			return b.val == val && b.mask == mask;
		}
		return false;
	}

	@Override
	public int hashCode() {
		long x = val ^ mask;
		return (int)x ^ (int)(x >>> 32);
	}

	@Override
	public String toString() {
		if (equals(TRUE)) {
			return "TRUE";
		} else if (equals(FALSE)) {
			return "FALSE";
		} //else if (bitSize == 64 && msb()) {
			//return unsignedBigValue().toString(16) + '_' + bitSize;
		//}
		return "0x" + Long.toHexString(zExtLongValue()) + '_' + bitSize;
	}

	@Override
	public int compareTo(BitNumber o) {
		if (ult(o)) {
			return -1;
		}
		if (equals(o)) {
			return 0;
		}
		return 1;
	}

	/**
	 * Create a new number of the given size.
	 *
	 * @param w The payload.
	 * @param bitSize The size.
	 * @return The word.
	 */
	public static BitNumber valueOf(long w, int bitSize) {
		Statistic.countBitNumberUse();
		BitNumber tmp = new BitNumber(w, bitSize);
		WeakReference<BitNumber> found = cache.get(tmp);
		if (found == null) {
			cache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		BitNumber result = found.get();
		if (result == null) {
			Statistic.countBitNumberUse();
			cache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		Statistic.countBitNumberReuse();
		return result;
	}

	/**
	 * Create a new number.
	 *
	 * @param val The payload.
	 * @return The word.
	 */
	public static BitNumber valueOf(RTLNumber val) {
		return valueOf(val.longValue(), val.getBitWidth());
	}

	/**
	 * Create a new number of the same size as the current one.
	 *
	 * @param val The payload.
	 * @return The new instance.
	 */
	public BitNumber valueOf(long val) {
		return valueOf(val, bitSize);
	}

	/**
	 * Create a new number corresponding to the given boolean.
	 *
	 * @param val The payload.
	 * @return The new instance.
	 */
	public static BitNumber valueOf(boolean val) {
		Statistic.countBitNumberUse();
		Statistic.countBitNumberReuse();
		return val ? TRUE : FALSE;
	}

	@Override
	public int getBitWidth() {
		return bitSize;
	}

	/**
	 * Return the log2 of a number if it is a power of 2, otherwise return none.
	 *
	 * @return The result.
	 */
	public Optional<Integer> log2n() {
		assert val != 0L;
		int z = Long.numberOfTrailingZeros(val);
		assert z < bitSize;
		if (val == bit(z)) {
			return Optional.optional(z);
		} else {
			return Optional.none();
		}
	}
}
