package org.jakstab.analysis.newIntervals;

import org.jakstab.JOption;
import org.jakstab.Options;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.newIntervals.word.Word;
import org.jakstab.analysis.newIntervals.word.Word64;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.*;

import java.math.BigInteger;
import java.util.*;

public class Interval implements Comparable<Interval>, AbstractState, AbstractValue, BitVectorType, Iterable<Long> {

	private static final Logger logger = Logger.getLogger(Interval.class);

	private static final JOption<Integer> maxConcretizationSize = JOption.create("interval-concretization-threshold", "k", 20, "Sets the maximum concretization size for intervals.");

	private final Word minBits;
	private final Word maxBits;
	private final Bits bits;
	private final IntervalKind kind;

	private static final Map<Bits, Interval> botIntervals = new EnumMap<>(Bits.class);
	private static final Map<Bits, Interval> topIntervals = new EnumMap<>(Bits.class);
	private static final Interval[] emptySet = {};

	public static final Interval TRUE_INTERVAL = mkSomeInterval(~0L, ~0L, Bits.BIT1);
	public static final Interval FALSE_INTERVAL = mkSomeInterval(0L, 0L, Bits.BIT1);
	public static final Interval BOTH_INTERVAL = mkTopInterval(Bits.BIT1);

	private Interval(Word minBits, Word maxBits, Bits bits, IntervalKind kind, boolean allowPromote) {
		super();
		assert bits != null;
		assert kind != null;
		assert kind != IntervalKind.INTERVAL || minBits != null && maxBits != null;

		this.bits = bits;

		if (allowPromote && kind == IntervalKind.INTERVAL && minBits.equals(maxBits.add(Word.valueOf(1L, bits)))) {
			this.minBits = null;
			this.maxBits = null;
			this.kind = IntervalKind.TOP;
			logger.debug("Promoting (|" + minBits + ", " + maxBits + "|)_" + bits + " to TOP");
		} else {
			this.minBits = minBits;
			this.maxBits = maxBits;
			this.kind = kind;
		}
		logger.debug("Created new interval " + this);
	}

	private Interval(RTLNumber n, Bits bits) {
		this(Word.valueOf(n.longValue(), bits), Word.valueOf(n.longValue(), bits), bits, IntervalKind.INTERVAL, true);
	}

	Interval(RTLNumber n) {
		this(n, Bits.fromInt(n.getBitWidth()));
	}

	public static Interval mkTopInterval(Bits bits) {
		Interval i = topIntervals.get(bits);
		if (i == null) {
			i = new Interval(null, null, bits, IntervalKind.TOP, true);
			topIntervals.put(bits, i);
		}
		return i;
	}

	public static Interval mkBotInterval(Bits bits) {
		Interval i = botIntervals.get(bits);
		if (i == null) {
			i = new Interval(null, null, bits, IntervalKind.BOT, true);
			botIntervals.put(bits, i);
		}
		return i;
	}

	private static Interval mkSomeInterval(long min, long max, Bits bits) {
		Word minW = Word.valueOf(min, bits);
		Word maxW = Word.valueOf(max, bits);
		return new Interval(minW, maxW, bits, IntervalKind.INTERVAL, true);
	}

	private static Interval mkSpecificInterval(long min, long max, Bits bits) {
		Word minW = Word.valueOf(min, bits);
		Word maxW = Word.valueOf(max, bits);
		return new Interval(minW, maxW, bits, IntervalKind.INTERVAL, false);
	}

	private static Interval mkSomeInterval(Word min, Word max, Bits bits) {
		return mkSomeInterval(min.longValue(), max.longValue(), bits);
	}

	@Override
	public int compareTo(Interval t) {
		assert bits == t.bits;
		if (kind != t.kind) {
			return kind.compareTo(t.kind);
		} else if (kind == IntervalKind.INTERVAL) {
			return minBits.equals(t.minBits) ? maxBits.compareTo(t.maxBits) : minBits.compareTo(t.minBits);
		} else {
			return 0;
		}
	}

	@Override
	public boolean equals(Object o) {
		return o != null && o instanceof Interval && compareTo((Interval) o) == 0;
	}

	@Override
	public int hashCode() {
		return kind.hashCode() ^ bits.hashCode() ^ minBits.hashCode() ^ maxBits.hashCode();
	}

	@Override
	public String toString() {
		return getIdentifier();
	}

	@Override
	public int getBitWidth() {
		return bits.getBitWidth();
	}

	@Override
	public Set<RTLNumber> concretize() {
		if (isBot()) {
			return Collections.emptySet();
		}
		if (isTop()) {
			return RTLNumber.ALL_NUMBERS;
		}
		Set<RTLNumber> s = new FastSet<>();
		for (Long l : this) {
			s.add(ExpressionFactory.createNumber(l, bits.getBits()));
		}
		return s;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !isTop() && !isBot() && minBits.equals(maxBits);
	}

	public long getUniqueConcretization() {
		assert hasUniqueConcretization();
		return minBits.longValue();
	}

	@Override
	public Interval join(LatticeElement l) {
		Interval t = (Interval) l;
		assertCompatible(t);
		final Interval result;
		if (lessOrEqual(t)) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (t.isElement(minBits) && t.isElement(maxBits) && isElement(t.minBits) && isElement(t.maxBits)) {
			result = mkTopInterval(bits);
		} else if (t.isElement(maxBits) && isElement(t.minBits)) {
			result = mkSomeInterval(minBits, t.maxBits, bits);
		} else if (isElement(t.maxBits) && t.isElement(minBits)) {
			result = mkSomeInterval(t.minBits, maxBits, bits);
		} else {
			BigInteger r1 = internalSize(maxBits, t.minBits);
			BigInteger r2 = internalSize(t.maxBits, minBits);
			int cmp = r1.compareTo(r2);
			if (cmp < 0 || cmp == 0 && minBits.lessThan(t.minBits)) {
				result = mkSomeInterval(minBits, t.maxBits, bits);
			} else {
				result = mkSomeInterval(t.minBits, maxBits, bits);
			}
		}
		logger.debug("Joining " + this + " and " + t + " to " + result);
		assert lessOrEqual(result) && t.lessOrEqual(result) : "join returned something which is not greater or equal";
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		Interval t = (Interval) l;
		return isSubsetOf(t);
	}

	@Override
	public boolean isTop() {
		return kind == IntervalKind.TOP;
	}

	@Override
	public boolean isBot() {
		return kind == IntervalKind.BOT;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return projectionFromConcretization(expressions, new IntervalValuationState());
	}

	public static Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression[] expressions, IntervalValuationState s) {
		logger.debug("projection from concretization for " + expressions.length + " expressions: " + Arrays.toString(expressions));
		Tuple<Set<RTLNumber>> cValues = new Tuple<>(expressions.length);
		for (int i = 0; i < expressions.length; i++) {
			Interval aValue = abstractEval(expressions[i], s);
			logger.debug("expression: " + expressions[i] + " evaluated to: " + aValue + " (isTop: " + aValue.isTop() + ')');
			if (aValue.isTop()) {
				//is Boolean expression?
				if (expressions[i].getBitWidth() == 1) {
					Set<RTLNumber> tmp = new FastSet<>(2);
					Collections.addAll(tmp, ExpressionFactory.TRUE, ExpressionFactory.FALSE);
					cValues.set(i, tmp);
				} else {
					cValues.set(i, RTLNumber.ALL_NUMBERS);
				}
			} else {
				int k = 0;
				Set<RTLNumber> tmp = new FastSet<>(k);
				for (Long l : aValue) {
					k++;
					if (k > maxConcretizationSize.getValue()) {
						logger.debug("limiting " + aValue + " with " + aValue.size() + " elements to " + maxConcretizationSize.getValue() + " elements");
						tmp = RTLNumber.ALL_NUMBERS;
						break;
					} else {
						tmp.add(ExpressionFactory.createNumber(l, aValue.bits.getBits()));
					}
				}
				cValues.set(i, tmp);
			}
		}
		Set<Tuple<RTLNumber>> result = Sets.crossProduct(cValues);
		logger.debug("Projected " + result);
		return result;
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public String getIdentifier() {
		if (isTop()) {
			return "TOP";
		} else if (isBot()) {
			return "BOT";
		} else {
			return "(|" + minBits + ", " + maxBits + "|)_" + bits.getBits();
		}
	}

	/**
	 * Get the size of the interval.
	 *
	 * @return The number of elements in the interval. It can be larger than a long, so it is returned as a BigInteger.
	 */
	public BigInteger size() {
		final BigInteger size;
		if (isTop()) {
			size = BigInteger.valueOf(2L).pow(bits.getBits());
		} else if (isBot()) {
			size = BigInteger.ZERO;
		} else {
			size = internalSize(minBits, maxBits);
		}
		logger.debug("Size of " + this + " is " + size);
		return size;
	}

	private static BigInteger internalSize(Word min, Word max) {
		return Word64.wordToBigInteger(max.sub(min).inc().longValue());
	}

	/**
	 * Invert this interval.
	 */
	public Interval invert() {
		final Interval result;
		switch (kind) {
			case BOT:
				result = mkTopInterval(bits);
				break;
			case TOP:
				result = mkBotInterval(bits);
				break;
			default:
				result = mkSomeInterval(maxBits.inc(), minBits.dec(), bits);
				break;
		}
		logger.debug("Inverting " + this + " to " + result);
		return result;
	}

	/**
	 * Check if a value is in the interval.
	 *
	 * @param e The value.
	 * @return True if the value is in the interval.
	 */
	private boolean isElement(long e) {
		assert bits.narrow(e) == e : "bad call to isElement with " + e + " (" + bits.narrow(e) + ", " + bits + ')';
		return isElement(Word.valueOf(e, bits));
	}

	/**
	 * Check if a value is in the interval.
	 *
	 * @param e The value.
	 * @return True if the value is in the interval.
	 */
	public boolean isElement(RTLNumber e) {
		Bits eBits = Bits.fromInt(e.getBitWidth());
		assert bits == eBits : "Wrong bit-size. Got " + eBits + ", but expected " + bits;
		return isElement(e.longValue());
	}

	/**
	 * Check if a value is in the interval.
	 *
	 * @param e The value.
	 * @return True if the value is in the interval.
	 */
	public boolean isElement(Word e) {
		assert Word.valueOf(e, bits).equals(e);
		boolean result = isTop() || !isBot() && Bits.leq(minBits, e, maxBits);
		logger.debug(e + " element of " + this + ": " + result);
		if (hasUniqueConcretization()) {
			if ( (e.longValue() == getUniqueConcretization()) != result ) {
				logger.debug(isTop());
				logger.debug(isBot());
				logger.debug(Bits.leq(minBits, e, maxBits));
			}
			assert (e.longValue() == getUniqueConcretization()) == result : "isElement for single-element interval broken for " + this + " and " + e;
		}
		return result;
	}

	/**
	 * Assert that the given interval is compatible with the current one.
	 *
	 * @param t The interval to check.
	 */
	private void assertCompatible(Interval t) {
		assert bits == t.bits;
	}

	/**
	 * Check if this interval is a sub-interval of another interval.
	 *
	 * @param t The interval to check.
	 * @return True if the interval is a sub-interval.
	 */
	public boolean isSubsetOf(Interval t) {
		assertCompatible(t);
		final boolean result;
		if (isBot() || t.isTop()) {
			result = true;
		} else if (isTop() || t.isBot()) {
			result = false;
		} else if (minBits.equals(t.minBits) && maxBits.equals(t.maxBits)) {
			// take care of equal intervals, this was not in the original paper!
			logger.debug("Comparing equal intervals...");
			result = true;
		} else {
			result = t.isElement(minBits) && t.isElement(maxBits) && (!isElement(t.minBits) || !isElement(t.maxBits));
		}
		logger.debug(this + " is a subset of " + t + ": " + result);
		return result;
	}

	private Interval meet(Interval t) {
		return invert().join(t.invert()).invert();
	}

	private Interval gap(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (kind == IntervalKind.INTERVAL && t.kind == IntervalKind.INTERVAL && !t.isElement(maxBits) && !isElement(t.minBits)) {
			result = mkSomeInterval(t.minBits, maxBits, bits).invert();
		} else {
			result = mkBotInterval(bits);
		}
		logger.debug("Gap between " + this + " and " + t + " = " + result);
		return result;
	}

	private Interval extent(Interval t) {
		assertCompatible(t);
		Interval result;
		if (lessOrEqual(t)) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (t.isElement(minBits) && t.isElement(maxBits) && isElement(t.minBits) && isElement(t.maxBits)) {
			result = mkTopInterval(bits);
		} else if (t.isElement(maxBits) && isElement(t.minBits)) {
			result = mkSomeInterval(minBits, t.maxBits, bits);
		} else if (isElement(t.maxBits) && t.isElement(minBits)) {
			result = mkSomeInterval(t.minBits, maxBits, bits);
		} else {
			result = mkSomeInterval(minBits, t.maxBits, bits);
		}
		logger.debug("Extending " + this + " with " + t + " = " + result);
		return result;
	}

	private static Interval bigger(Interval s, Interval t) {
		s.assertCompatible(t);
		Interval result = t.size().compareTo(s.size()) > 0 ? t : s;
		logger.debug("Bigger of " + s + " and " + t + " = " + result);
		return result;
	}

	public static Interval joins(Collection<Interval> c) {
		List<Interval> s = new ArrayList<>(c.size());
		for (Interval e : c) {
			s.add(e);
		}
		Collections.sort(s);
		logger.debug("** starting joins of " + s);
		Bits bits = s.iterator().next().bits;
		Interval f = mkBotInterval(bits);
		Interval g = mkBotInterval(bits);
		for (Interval e : s) {
			if (e.kind == IntervalKind.TOP || e.kind == IntervalKind.INTERVAL && Bits.leq(Word.valueOf(0L, bits), e.maxBits, e.minBits)) {
				f.extent(e);
			}
		}
		for (Interval e : s) {
			g = bigger(g, f.gap(e));
			f = f.extent(e);
		}
		Interval result = bigger(f, g);
		logger.debug("Joins of " + s + " = " + result);
		for (Interval e : s) {
			assert e.lessOrEqual(result) : "joins returned something not in the interval";
		}
		return result;
	}

	public Interval[] intersection(Interval t) {
		assertCompatible(t);
		final Interval[] result;
		if (isBot() || t.isBot()) {
			result = emptySet;
		} else if (equals(t) || isTop()) {
			result = new Interval[]{t};
		} else if (t.isTop()) {
			result = new Interval[]{this};
		} else {
			boolean minInT = t.isElement(minBits);
			boolean maxInT = t.isElement(maxBits);
			boolean tMinInThis = isElement(t.minBits);
			boolean tMaxInThis = isElement(t.maxBits);
			if (minInT && maxInT && tMinInThis && tMaxInThis) {
				result = new Interval[]{mkSomeInterval(minBits, t.maxBits, bits), mkSomeInterval(maxBits, t.minBits, bits)};
			} else if (minInT && maxInT) {
				result = new Interval[]{this};
			} else if (tMinInThis && tMaxInThis) {
				result = new Interval[]{t};
			} else if (minInT && tMaxInThis) {
				result = new Interval[]{mkSomeInterval(minBits, t.maxBits, bits)};
			} else if (maxInT && tMinInThis) {
				result = new Interval[]{mkSomeInterval(maxBits, t.minBits, bits)};
			} else {
				result = emptySet;
			}
		}
		logger.debug("Intersection of " + this + " and " + t + " = " + Arrays.toString(result));
		return result;
	}

	public Interval addInterval(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot() || t.isBot()) {
			result = mkBotInterval(bits);
		} else if (isTop() || t.isTop()) {
			result = mkTopInterval(bits);
		} else if (size().add(t.size()).compareTo(BigInteger.valueOf(2L).pow(bits.getBits())) <= 0) {
			result = mkSomeInterval(minBits.add(t.minBits), maxBits.add(t.maxBits), bits);
		} else {
			result = mkTopInterval(bits);
		}
		logger.debug(this + " + " + t + " = " + result);
		return result;
	}

	public Interval subInterval(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot() || t.isBot()) {
			result = mkBotInterval(bits);
		} else if (size().add(t.size()).compareTo(BigInteger.valueOf(2L).pow(bits.getBits())) <= 0) {
			result = mkSomeInterval(minBits.sub(t.maxBits), maxBits.sub(t.minBits), bits);
		} else {
			result = mkTopInterval(bits);
		}
		logger.debug(this + " - " + t + " = " + result);
		return result;
	}

	public Interval negateInterval() {
		Interval result = mkSomeInterval(0L, 0L, bits).subInterval(this);
		logger.debug("-" + this + " = " + result);
		return result;
	}

	private Interval getNorthPole() {
		long max = 1L << bits.getBits() - 1;
		long min = max - 1L;
		return mkSomeInterval(min, max, bits);
	}

	private Interval getSouthPole() {
		return mkSomeInterval(bits.getMask(), 0L, bits);
	}

	/**
	 * Split an interval at the north pole.
	 *
	 * @return All sub-intervals.
	 */
	private Interval[] splitNorth() {
		final Interval[] result;
		if (isBot()) {
			result = emptySet;
		} else {
			long tmp = 1L << bits.getBits() - 1;
			if (isTop()) {
				result = new Interval[]{mkSomeInterval(0L, tmp - 1L, bits), mkSomeInterval(tmp, bits.getMask(), bits)};
			} else if (!getNorthPole().isSubsetOf(this)) {
				result = new Interval[]{this};
			} else {
				result = new Interval[]{mkSomeInterval(minBits.unsafeInternalValue(), tmp - 1L, bits), mkSomeInterval(tmp, maxBits.unsafeInternalValue(), bits)};
			}
		}
		logger.debug("Splitting " + this + " at the north pole = " + Arrays.toString(result));
		return result;
	}

	/**
	 * Split an interval at the south pole.
	 *
	 * @return All sub-intervals.
	 */
	private Interval[] splitSouth() {
		final Interval[] result;
		if (isBot()) {
			result = emptySet;
		} else if (isTop()) {
			long tmp = 1L << bits.getBits() - 1;
			result = new Interval[]{mkSomeInterval(tmp, bits.getMask(), bits), mkSomeInterval(0L, tmp - 1L, bits)};
		} else if (!getSouthPole().isSubsetOf(this)) {
			result = new Interval[]{this};
		} else {
			result = new Interval[]{mkSomeInterval(0L, maxBits.unsafeInternalValue(), bits), mkSomeInterval(minBits.unsafeInternalValue(), bits.getMask(), bits)};
		}
		logger.debug("Splitting " + this + " at the south pole = " + Arrays.toString(result));
		return result;
	}

	private Set<Interval> cut() {
		Set<Interval> result = new FastSet<>();
		for (Interval u : splitNorth()) {
			Collections.addAll(result, u.splitSouth());
		}
		logger.debug("Cutting " + this + " = " + result);
		return result;
	}

	private Interval extentBitSize() {
		switch (bits) {
			case BIT1:
				assert !Options.failFast.getValue() : "Extending 1-bit interval";
				logger.warn("Extending 1-bit interval!");
				return mkSomeInterval(minBits, maxBits, Bits.BIT8);
			case BIT8:
				return mkSomeInterval(minBits, maxBits, Bits.BIT16);
			case BIT16:
				return mkSomeInterval(minBits, maxBits, Bits.BIT32);
			case BIT32:
				return mkSomeInterval(minBits, maxBits, Bits.BIT64);
			case BIT64:
				return this;
		}
		assert !Options.failFast.getValue() : "Extending unknown interval size";
		return this;
	}

	private Interval mul_u(Interval t) {
		assertCompatible(t);
		BigInteger a = minBits.bigValue();
		BigInteger b = maxBits.bigValue();
		BigInteger c = t.minBits.bigValue();
		BigInteger d = t.maxBits.bigValue();
		final Interval result;
		if (b.multiply(d).subtract(a.multiply(c)).compareTo(BigInteger.valueOf(2L).pow(bits.getBits())) == -1) {
			result = mkSomeInterval(minBits.mul(t.minBits), maxBits.mul(t.maxBits), bits);
		} else {
			result = mkTopInterval(bits);
		}
		logger.debug(this + " x_u " + t + " = " + result);
		return result;
	}

	private Interval mul_s(Interval t) {
		assertCompatible(t);
		BigInteger a = minBits.bigValue();
		BigInteger b = maxBits.bigValue();
		BigInteger c = t.minBits.bigValue();
		BigInteger d = t.maxBits.bigValue();
		BigInteger twoW = BigInteger.valueOf(2L).pow(bits.getBits());
		boolean a_msb = minBits.msb();
		boolean b_msb = maxBits.msb();
		boolean c_msb = t.minBits.msb();
		boolean d_msb = t.maxBits.msb();
		final Interval result;
		if (a_msb == b_msb && b_msb == c_msb && c_msb == d_msb && b.multiply(d).subtract(a.multiply(c)).compareTo(twoW) == -1) {
			result = mkSomeInterval(minBits.mul(t.minBits), maxBits.mul(t.maxBits), bits);
		} else if (a_msb && b_msb && !c_msb && !d_msb && b.multiply(c).subtract(a.multiply(d)).compareTo(twoW) == -1) {
			result = mkSomeInterval(minBits.mul(t.maxBits), maxBits.mul(t.minBits), bits);
		} else if (!a_msb && !b_msb && c_msb && d_msb && a.multiply(d).subtract(b.multiply(c)).compareTo(twoW) == -1) {
			result = mkSomeInterval(maxBits.mul(t.minBits), minBits.mul(t.maxBits), bits);
		} else {
			result = mkTopInterval(bits);
		}
		logger.debug(this + " x_s " + t + " = " + result);
		return result;
	}

	private Interval[] mul_us(Interval t) {
		Interval[] result = mul_u(t).intersection(mul_s(t));
		logger.debug(this + " x_us " + t + " = " + Arrays.toString(result));
		return result;
	}

	public Interval mulInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> s = new FastSet<>();
		for (Interval u : cut()) {
			Interval us = u.extentBitSize();
			for (Interval v : t.cut()) {
				Collections.addAll(s, us.mul_us(v.extentBitSize()));
			}
		}
		Interval result = joins(s);
		logger.debug(this + " * " + t + " = " + result);
		return result;
	}

	/**
	 * Remove the (|0, 0|) interval from the border of an interval.
	 *
	 * @return The interval without 0.
	 */
	private Interval removeZero() {
		if (minBits.unsafeInternalValue() == 0L) {
			assert maxBits.unsafeInternalValue() != 0L : "removeZero on (|0, 0|)";
			return mkSomeInterval(minBits.inc(), maxBits, bits);
		} else if (maxBits.unsafeInternalValue() == 0L) {
			assert minBits.unsafeInternalValue() != 0L : "removeZero on (|0, 0|)";
			return mkSomeInterval(minBits, maxBits.dec(), bits);
		} else {
			assert !isElement(0L) : "interval contains a 0";
			return this;
		}
	}

	private Interval div_u(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		Interval result = mkSomeInterval(minBits.udiv(t.maxBits), maxBits.udiv(t.minBits), bits);
		logger.debug(this + " /_u " + t + " = " + result);
		return result;
	}

	public Interval unsignedDivInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v0 : t.splitSouth()) {
				Interval v = v0.removeZero();
				results.add(u.div_u(v));
			}
		}
		Interval result = joins(results);
		logger.debug(this + " /u " + t + " = " + result);
		return result;
	}

	private Interval div_s(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final Interval result;
		boolean msb1 = minBits.msb();
		boolean msb2 = t.minBits.msb();
		if (!msb1 && !msb2) {
			result = mkSomeInterval(minBits.sdiv(t.maxBits), maxBits.sdiv(t.minBits), bits);
		} else if (msb1 && msb2) {
			result = mkSomeInterval(maxBits.sdiv(t.minBits), minBits.sdiv(t.maxBits), bits);
		} else if (!msb1) {
			result = mkSomeInterval(maxBits.sdiv(t.maxBits), minBits.sdiv(t.minBits), bits);
		} else {
			result = mkSomeInterval(minBits.sdiv(t.minBits), maxBits.sdiv(t.maxBits), bits);
		}
		logger.debug(this + " /_s " + t + " = " + result);
		return result;
	}

	public Interval signedDivInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> results = new FastSet<>();
		for (Interval u : cut()) {
			for (Interval v0 : t.cut()) {
				Interval v = v0.removeZero();
				results.add(u.div_s(v));
			}
		}
		Interval result = joins(results);
		logger.debug(this + " /s " + t + " = " + result);
		return result;
	}

	private Interval amb() {
		assert kind == IntervalKind.INTERVAL;
		return mkSomeInterval(Word.valueOf(0L, bits), maxBits.dec(), bits);
	}

	private Interval rem_u(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final Interval result;
		Interval divided = div_u(t);
		if (divided.size().equals(BigInteger.ONE)) {
			result = subInterval(divided).mulInterval(t);
		} else {
			result = t.amb();
		}
		logger.debug(this + " %_u " + t + " = " + result);
		return result;
	}

	public Interval unsignedRemInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v0 : t.splitSouth()) {
				Interval v = v0.removeZero();
				results.add(u.rem_u(v));
			}
		}
		Interval result = joins(results);
		logger.debug(this + " %u " + t + " = " + result);
		return result;
	}

	private Interval rem_s(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final Interval result;
		Interval divided = div_s(t);
		if (divided.size().equals(BigInteger.ONE)) {
			result = subInterval(divided).mulInterval(t);
		} else {
			assert minBits.sign().equals(maxBits.sign()) : "Signs do not equal";
			assert t.minBits.sign().equals(t.maxBits.sign()) : "Signs do not equal";
			Word thisSign = minBits.sign();
			Word tSign = t.minBits.sign();
			result = mkSomeInterval(thisSign, thisSign, bits).mulInterval(mkSomeInterval(tSign, tSign, bits).mulInterval(t));
		}
		logger.debug(this + " %_s " + t + " = " + result);
		return result;
	}

	public Interval signedRemInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v0 : t.splitSouth()) {
				Interval v = v0.removeZero();
				results.add(u.rem_s(v));
			}
		}
		Interval result = joins(results);
		logger.debug(this + " %s " + t + " = " + result);
		return result;
	}

	private static Word minOr(Word a, Word b, Word c, Word d, Bits bits) {
		Word m = Word.valueOf(1L << bits.getBitWidth() - 1, bits);
		while (m.longValue() != 0L) {
			if (a.not().and(c).and(m).longValue() != 0L) {
				Word e = a.or(m).and(m.negate());
				if (e.lessThanOrEqual(b)) {
					return e.or(c);
				}
			} else if (a.and(c.not()).and(m).longValue() != 0L) {
				Word e = c.or(m).and(m.negate());
				if (e.lessThanOrEqual(d)) {
					return a.or(e);
				}
			}
			m = m.shr(1);
		}
		return a.or(c);
	}

	private static Word maxOr(Word a, Word b, Word c, Word d, Bits bits) {
		Word m = Word.valueOf(1L << bits.getBitWidth() - 1, bits);
		while (m.longValue() != 0L) {
			if (b.and(d).and(m).longValue() != 0L) {
				Word e = b.sub(m).or(m.dec());
				if (e.greaterThanOrEqual(a)) {
					return e.or(d);
				}
				Word f = d.sub(m).or(m.dec());
				if (f.greaterThanOrEqual(c)) {
					return b.or(f);
				}
			}
			m = m.shr(1);
		}
		return b.or(d);
	}

	private Interval orW(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		Word min = minOr(minBits, maxBits, t.minBits, t.maxBits, bits);
		Word max = maxOr(minBits, maxBits, t.minBits, t.maxBits, bits);
		Interval result = mkSomeInterval(min, max, bits);
		logger.debug(this + " |w " + t + " = " + result);
		return result;
	}

	public Interval orInterval(Interval t) {
		assertCompatible(t);
		Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v : t.splitSouth()) {
				results.add(u.orW(v));
			}
		}
		Interval result = joins(results);
		logger.debug(this + " | " + t + " = " + result);
		return result;
	}

	private Interval andW(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		Word min = null; //TODO
		Word max = null; //TODO
		Interval result = mkSomeInterval(min, max, bits);
		logger.debug(this + " &w " + t + " = " + result);
		return result;
	}

	public Interval andInterval(Interval t) {
		assertCompatible(t);
		/*Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v : t.splitSouth()) {
				results.add(u.andW(v));
			}
		}
		Interval result = joins(results);*/
		Interval result = notInterval().orInterval(t.notInterval()).notInterval(); // ~(~a | ~b)
		logger.debug(this + " & " + t + " = " + result);
		return result;
	}

	private Interval xorW(Interval t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		Word min = null; //TODO
		Word max = null; //TODO
		Interval result = mkSomeInterval(min, max, bits);
		logger.debug(this + " ^w " + t + " = " + result);
		return result;
	}

	public Interval xorInterval(Interval t) {
		assertCompatible(t);
		/*Set<Interval> results = new FastSet<>();
		for (Interval u : splitSouth()) {
			for (Interval v : t.splitSouth()) {
				results.add(u.xorW(v));
			}
		}
		Interval result = joins(results);*/
		Interval result = andInterval(t).orInterval(notInterval().andInterval(t.notInterval())).notInterval(); // ~((a & b) | (~a & ~b))
		logger.debug(this + " ^ " + t + " = " + result);
		return result;
	}

	public Interval notInterval() {
		Interval result = addInterval(mkSomeInterval(1L, 1L, bits)).negateInterval();
		logger.debug("~" + this + " = " + result);
		return result;
	}

	public Interval signExtendInterval(long firstBit, long lastBit) {
		assert firstBit > 0L && firstBit <= 64L : "Invalid first bit " + firstBit;
		assert lastBit > 0L && lastBit <= 64L : "Invalid last bit " + lastBit;
		assert Bits.fromInt((int)firstBit - 1) == bits;
		return signExtendInterval(Bits.fromInt((int)lastBit));
	}

	public Interval signExtendInterval(Bits bits) {
		assert bits.getBitWidth() >= this.bits.getBitWidth();
		Set<Interval> results = new FastSet<>();
		for (Interval i : splitNorth()) {
			assert i.kind == IntervalKind.INTERVAL;
			results.add(mkSomeInterval(i.minBits, i.maxBits, bits));
		}
		Interval result = joins(results);
		logger.debug(this + " `signExtend` " + bits + " = " + result);
		return result;
	}

	public Interval zeroExtendInterval(long firstBit, long lastBit) {
		assert firstBit > 0L && firstBit <= 64L : "Invalid first bit " + firstBit;
		assert lastBit > 0L && lastBit <= 64L : "Invalid last bit " + lastBit;
		assert Bits.fromInt((int)firstBit - 1) == bits;
		return zeroExtendInterval(Bits.fromInt((int)lastBit));
	}

	public Interval zeroExtendInterval(Bits bits) {
		assert bits.getBitWidth() >= this.bits.getBitWidth();
		Set<Interval> results = new FastSet<>();
		for (Interval i : splitSouth()) {
			assert i.kind == IntervalKind.INTERVAL;
			results.add(mkSomeInterval(i.minBits.unsafeInternalValue(), i.maxBits.unsafeInternalValue(), bits));
		}
		Interval result = joins(results);
		logger.debug(this + " `zeroExtend` " + bits + " = " + result);
		return result;
	}

	private Interval truncate(int bitWidth) {
		assert bitWidth <= bits.getBitWidth();
		if (isBot() || isTop()) {
			return this;
		} else {
			Word a = minBits.shr(bitWidth);
			Word b = maxBits.shr(bitWidth);
			Word mask = Word.valueOf((1L << bitWidth - 1) - 1L, bits);
			Word tMin = minBits.and(mask);
			Word tMax = maxBits.and(mask);
			if (a.equals(b) && tMin.lessThanOrEqual(tMax)) {
				return mkSomeInterval(tMin, tMax, bits);
			} else {
				a = a.inc();
				if (a.equals(b) && !tMin.lessThanOrEqual(tMax)) {
					return mkSomeInterval(tMin, tMax, bits);
				} else {
					return mkTopInterval(bits);
				}
			}
		}
	}

	public Interval truncateInterval(Bits bits) {
		Interval result = truncate(bits.getBitWidth());
		if (result.kind == IntervalKind.INTERVAL) {
			result = mkSomeInterval(result.minBits, result.maxBits, bits);
		}
		logger.debug(this + " `truncate` " + bits + " = " + result);
		return result;
	}

	public Interval shlInterval(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot()) {
			result = mkBotInterval(bits);
		} else {
			if (t.hasUniqueConcretization()) {
				long kl = t.getUniqueConcretization();
				long w = (long)bits.getBitWidth();
				if (kl < w && kl > -w) {
					logger.warn("Shift by too large size: " + kl + ", type: " + bits);
				}
				kl = kl % w;
				int k = (int)kl;
				Interval tmp = truncate(bits.getBitWidth() - k);
				if (tmp.kind == IntervalKind.INTERVAL) {
					result = mkSomeInterval(tmp.minBits.shl(k), tmp.maxBits.shl(k), bits);
				} else {
					long maxVal = bits.getMask() ^ (1L << kl - 1L) - 1L;
					result = mkSomeInterval(0L, maxVal, bits);
				}
			} else {
				result = mkTopInterval(bits);
			}
		}
		logger.debug(this + " << " + t + " = " + result);
		return result;
	}

	public Interval shrInterval(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot()) {
			result = mkBotInterval(bits);
		} else {
			if (t.hasUniqueConcretization()) {
				long kl = t.getUniqueConcretization();
				long w = (long) bits.getBitWidth();
				if (kl < w && kl > -w) {
					logger.warn("Shift by too large size: " + kl + ", type: " + bits);
				}
				kl = kl % w;
				int k = (int)kl;
				if (getSouthPole().isSubsetOf(this)) {
					result = mkSomeInterval(0L, (1L << bits.getBitWidth() - k) - 1L, bits);
				} else {
					assert kind == IntervalKind.INTERVAL : "South pole was not in TOP?!";
					result = mkSomeInterval(minBits.longValue() >> k, maxBits.longValue() >> k, bits);
				}
			} else {
				result = mkTopInterval(bits);
			}
		}
		logger.debug(this + " >> " + t + " = " + result);
		return result;
	}

	public Interval sarInterval(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot()) {
			result = mkBotInterval(bits);
		} else {
			if (t.hasUniqueConcretization()) {
				long kl = t.getUniqueConcretization();
				long w = (long) bits.getBitWidth();
				if (kl < w && kl > -w) {
					logger.warn("Shift by too large size: " + kl + ", type: " + bits);
				}
				kl = kl % w;
				int k = (int)kl;
				if (getNorthPole().isSubsetOf(this)) {
					result = mkSomeInterval(0L, (1L << bits.getBitWidth() - k) - 1L, bits);
				} else {
					assert kind == IntervalKind.INTERVAL : "North pole was not in TOP?!";
					result = mkSomeInterval(minBits.longValue() >>> k, maxBits.longValue() >>> k, bits);
				}
			} else {
				result = mkTopInterval(bits);
			}
		}
		logger.debug(this + " >>> " + t + " = " + result);
		return result;
	}

	public Interval widen(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot()) {
			result = t;
		} else if (t.isBot() || isTop()) {
			result = this;
		} else if (t.isTop()) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (size().compareTo(BigInteger.valueOf(2L).pow(bits.getBits() - 1)) >= 0) {
			result = mkTopInterval(bits);
		} else {
			Interval tmp = join(t);
			Word one = Word.valueOf(1L, bits);
			Word two = Word.valueOf(2L, bits);
			if (tmp.equals(this)) {
				result = mkSomeInterval(minBits, t.maxBits, bits).join(
						mkSomeInterval(minBits, maxBits.mul(two).sub(minBits).add(one), bits));
			} else if (tmp.equals(t)) {
				result = mkSomeInterval(t.minBits, maxBits, bits).join(
						mkSomeInterval(minBits.mul(two).sub(maxBits).sub(one), maxBits, bits));
			} else if (t.isElement(minBits) && t.isElement(maxBits)) {
				result = t.join(mkSomeInterval(t.minBits, t.minBits.add(maxBits.mul(two)).sub(minBits.mul(two)).add(one), bits));
			} else {
				result = mkTopInterval(bits);
			}
		}
		logger.debug(this + " `widen` " + t + " = " + result);
		assert lessOrEqual(result) && t.lessOrEqual(result) : "Widen returned something smaller than one of the arguments";
		return result;
	}

	@Override
	public Iterator<Long> iterator() {
		if (isBot()) {
			return new BotIntervalIterator();
		} else if (isTop()) {
			final Interval i;
			switch (bits) {
				case BIT1:
					i = mkSpecificInterval(0L, 1L, bits);
					break;
				case BIT8:
					i = mkSpecificInterval(0L, 0xFFL, bits);
					break;
				case BIT16:
					i = mkSpecificInterval(0L, 0xFFFFL, bits);
					break;
				case BIT32:
					i = mkSpecificInterval(0L, 0xFFFFFFFFL, bits);
					break;
				case BIT64:
					i = mkSpecificInterval(0L, ~0L, bits);
					break;
				default:
					throw new UnsupportedOperationException("Can not iterate TOP-Interval of unknown size");
			}
			return i.iterator();
		} else {
			return new Iterator<Long>() {
				private Word pos = minBits;
				private boolean done = false;

				@Override
				public boolean hasNext() {
					return !done;
				}

				@Override
				public Long next() {
					if (hasNext()) {
						Long val = pos.longValue();
						done |= pos.equals(maxBits);
						pos = pos.inc();
						return val;
					} else {
						throw new NoSuchElementException("Iterated over complete interval");
					}
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException("Intervals are immutable");
				}
			};
		}
	}

	private static Pair<Interval, Interval> assumeULeq(Interval s, Interval t) {
		s.assertCompatible(t);
		Bits bits = s.bits;
		final Interval newS;
		if (t.isBot()) {
			newS = mkBotInterval(bits);
		} else if (t.isElement(bits.getMask())) {
			newS = s;
		} else {
			assert t.kind == IntervalKind.INTERVAL;
			newS = s.meet(mkSomeInterval(Word.valueOf(0L, bits), t.maxBits, bits));
		}
		final Interval newT;
		if (s.isBot()) {
			newT = mkBotInterval(bits);
		} else if (s.isElement(0L)) {
			newT = t;
		} else {
			assert s.kind == IntervalKind.INTERVAL;
			newT = t.meet(mkSomeInterval(s.minBits, Word.valueOf(bits.getMask(), bits), bits));
		}
		Pair<Interval, Interval> result = new Pair<>(newS, newT);
		logger.debug("assume " + s + " <= " + t + ": " + result);
		return result;
	}

	private static Pair<Interval, Interval> assumeSLeq(Interval s, Interval t) {
		s.assertCompatible(t);
		Bits bits = s.bits;
		final Interval newS;
		if (t.isBot()) {
			newS = mkBotInterval(bits);
		} else if (t.isElement(bits.getMask() >> 1L)) {
			newS = s;
		} else {
			assert t.kind == IntervalKind.INTERVAL;
			newS = s.meet(mkSomeInterval(Word.valueOf(1L << bits.getBitWidth() - 1, bits), t.maxBits, bits));
		}
		final Interval newT;
		if (s.isBot()) {
			newT = mkBotInterval(bits);
		} else if (s.isElement(1L << bits.getBitWidth() - 1)) {
			newT = t;
		} else {
			assert s.kind == IntervalKind.INTERVAL;
			newT = t.meet(mkSomeInterval(s.minBits, Word.valueOf(bits.getMask() >> 1L, bits), bits));
		}
		Pair<Interval, Interval> result = new Pair<>(newS, newT);
		logger.debug("assume " + s + " <= " + t + ": " + result);
		return result;
	}

	private static IntervalValuationState assumeNeq(RTLExpression arg, Interval newInt, IntervalValuationState newState) {
		if (arg instanceof RTLVariable) {
			if (newInt.hasUniqueConcretization()) {
				long val = newInt.getUniqueConcretization();
				RTLVariable var = (RTLVariable) arg;
				Interval oldInt = newState.getVariableValue(var);
				oldInt.assertCompatible(newInt);
				if (val == oldInt.minBits.longValue()) {
					if (val == oldInt.maxBits.longValue()) {
						newState.setVariableValue(var, mkBotInterval(oldInt.bits));
					} else {
						newState.setVariableValue(var, mkSomeInterval(oldInt.minBits.inc(), oldInt.maxBits, oldInt.bits));
					}
				} else if (val == oldInt.maxBits.longValue()) {
					newState.setVariableValue(var, mkSomeInterval(oldInt.minBits, oldInt.maxBits.dec(), oldInt.bits));
				} else {
					logger.debug("Can not use information in " + arg + ' ' + oldInt + " != " + newInt);
				}
			}
		} else if (arg instanceof RTLOperation) {
			RTLOperation e = (RTLOperation) arg;
			RTLExpression[] args = e.getOperands();
			switch (e.getOperator()) {
				case NEG:
					assert args.length == 1;
					newState = assumeNeq(args[0], newInt.negateInterval(), newState);
					break;
				case NOT:
					assert args.length == 1;
					newState = assumeNeq(args[0], newInt.notInterval(), newState);
					break;
				default:
					logger.warn("Ignoring equality in operation: " + arg + " != " + newInt);
			}
		} else {
			logger.warn("Ignoring equality: " + arg + " != " + newInt);
		}
		return newState;
	}


	private static IntervalValuationState assumeEq(RTLExpression arg, Interval newInt, IntervalValuationState newState) {
		if (arg instanceof RTLVariable) {
			RTLVariable var = (RTLVariable) arg;
			Interval oldInt = newState.getVariableValue(var);
			newState.setVariableValue(var, oldInt.meet(newInt));
		} else if (arg instanceof RTLOperation) {
			RTLOperation e = (RTLOperation) arg;
			RTLExpression[] args = e.getOperands();
			switch (e.getOperator()) {
				case NEG:
					assert args.length == 1;
					newState = assumeEq(args[0], newInt.negateInterval(), newState);
					break;
				case NOT:
					assert args.length == 1;
					newState = assumeEq(args[0], newInt.notInterval(), newState);
					break;
				case PLUS:
					assert args.length > 1;
					Interval[] iArgs = new Interval[args.length];
					for (int i = 0; i < args.length; i++) {
						iArgs[i] = abstractEval(args[i], newState);
					}
					for (int i = 0; i < args.length; i++) {
						Interval newRes = newInt;
						for (int j = 0; j < args.length; j++) {
							if (i != j) {
								newRes = newRes.subInterval(iArgs[j]);
							}
						}
						newState = assumeEq(args[i], newRes, newState);
					}
					break;
				default:
					logger.warn("Ignoring equality in operation: " + arg + " == " + newInt);
			}
		} else {
			logger.warn("Ignoring equality: " + arg + " == " + newInt);
		}
		return newState;
	}

	private static IntervalValuationState assumeFalse(RTLExpression e, IntervalValuationState newState) {
		Interval assumeVal = abstractEval(e, newState);
		logger.debug("Assuming " + e + " not to hold");
		assert !assumeVal.isBot() : "Bottoming state reached with " + e + " and " + newState;
		if (assumeVal.hasUniqueConcretization()) {
			assert assumeVal.getUniqueConcretization() == 0L : "Infeasible state reached with " + e + " and " + newState;
			logger.verbose(e + " is always false in " + newState);
			return newState;
		}
		if (e instanceof RTLOperation) {
			RTLOperation op = (RTLOperation) e;
			RTLExpression[] args = op.getOperands();
			Interval op0, op1;
			switch (op.getOperator()) {
				case UNKNOWN:
					assert !Options.failFast.getValue() : "Assuming UNKNOWN operator";
					return newState;
				case AND:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = newState.join(assumeFalse(arg, new IntervalValuationState(newState)));
					}
					return newState;
				case OR:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = assumeFalse(arg, newState);
					}
					return newState;
				case EQUAL:
					assert args.length == 2;
					op0 = abstractEval(args[0], newState);
					op1 = abstractEval(args[1], newState);
					newState = assumeNeq(args[0], op1, newState);
					newState = assumeNeq(args[1], op0, newState);
					return newState;
				case LESS:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createLessOrEqual(args[1], args[0]), newState);
				case LESS_OR_EQUAL:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createLessThan(args[1], args[0]), newState);
				case UNSIGNED_LESS:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createUnsignedLessOrEqual(args[1], args[0]), newState);
				case UNSIGNED_LESS_OR_EQUAL:
					assert args.length == 2;
					return assumeTrue(ExpressionFactory.createUnsignedLessThan(args[1], args[0]), newState);
				case NOT:
					assert args.length == 1;
					newState = assumeTrue(args[0], newState);
					return newState;
				default:
					logger.warn("assumeTrue: Unknown or unhandled operator " + op.getOperator() + " in assumption " + e);
					return newState;
			}
		} else if (e instanceof RTLBitRange) {
			assert !Options.failFast.getValue() : "Assuming a RTLBitRange is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLConditionalExpression) {
			RTLConditionalExpression c = (RTLConditionalExpression) e;
			RTLExpression cond = c.getCondition();
			RTLExpression negCond = ExpressionFactory.createNot(cond);
			RTLExpression t = c.getTrueExpression();
			RTLExpression f = c.getFalseExpression();
			return assumeFalse(ExpressionFactory.createOr(ExpressionFactory.createAnd(cond, t),ExpressionFactory.createAnd(negCond, f)), newState);
		} else if (e instanceof RTLMemoryLocation) {
			RTLMemoryLocation m = (RTLMemoryLocation) e;
			newState.setMemoryValue(m, FALSE_INTERVAL);
			return newState;
		} else if (e instanceof RTLNondet) {
			// this does not really help, but well...
			return newState;
		} else if (e instanceof RTLNumber) {
			throw new AssertionError("Number did not reduce to a constant: " + e);
		} else if (e instanceof RTLSpecialExpression) {
			assert !Options.failFast.getValue() : "Assuming a RTLSpecialExpression is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLVariable) {
			RTLVariable v = (RTLVariable) e;
			newState.setVariableValue(v, FALSE_INTERVAL);
			return newState;
		} else {
			throw new AssertionError("Unknown assumption " + e);
		}
	}

	private static IntervalValuationState assumeTrue(RTLExpression e, IntervalValuationState newState) {
		Interval assumeVal = abstractEval(e, newState);
		logger.debug("Assuming " + e + " to hold");
		assert !assumeVal.isBot() : "Bottoming state reached with " + e + " and " + newState;
		if (assumeVal.hasUniqueConcretization()) {
			assert assumeVal.getUniqueConcretization() != 0L : "Infeasible state reached with " + e + " and " + newState;
			logger.verbose(e + " is always true in " + newState);
			return newState;
		}
		if (e instanceof RTLOperation) {
			RTLOperation op = (RTLOperation) e;
			RTLExpression[] args = op.getOperands();
			Interval op0, op1;
			Pair<Interval, Interval> tmp;
			RTLExpression leq, eq;
			switch (op.getOperator()) {
				case UNKNOWN:
					assert !Options.failFast.getValue() : "Assuming UNKNOWN operator";
					return newState;
				case AND:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = assumeTrue(arg, newState);
					}
					return newState;
				case OR:
					assert args.length > 1;
					for (RTLExpression arg : args) {
						newState = newState.join(assumeTrue(arg, new IntervalValuationState(newState)));
					}
					return newState;
				case EQUAL:
					assert args.length == 2;
					op0 = abstractEval(args[0], newState);
					op1 = abstractEval(args[1], newState);
					newState = assumeEq(args[0], op1, newState);
					newState = assumeEq(args[1], op0, newState);
					return newState;
				case LESS:
					assert args.length == 2;
					leq = ExpressionFactory.createLessOrEqual(args[0], args[1]);
					eq = ExpressionFactory.createEqual(args[0], args[1]);
					return assumeTrue(ExpressionFactory.createAnd(leq, ExpressionFactory.createNot(eq)), newState);
				case LESS_OR_EQUAL:
					assert args.length == 2;
					op0 = abstractEval(args[0], newState);
					op1 = abstractEval(args[1], newState);
					tmp = assumeSLeq(op0, op1);
					newState = assumeEq(args[0], tmp.getLeft(), newState);
					newState = assumeEq(args[1], tmp.getRight(), newState);
					return newState;
				case UNSIGNED_LESS:
					assert args.length == 2;
					leq = ExpressionFactory.createUnsignedLessOrEqual(args[0], args[1]);
					eq = ExpressionFactory.createEqual(args[0], args[1]);
					return assumeTrue(ExpressionFactory.createAnd(leq, ExpressionFactory.createNot(eq)), newState);
				case UNSIGNED_LESS_OR_EQUAL:
					assert args.length == 2;
					op0 = abstractEval(args[0], newState);
					op1 = abstractEval(args[1], newState);
					tmp = assumeULeq(op0, op1);
					newState = assumeEq(args[0], tmp.getLeft(), newState);
					newState = assumeEq(args[1], tmp.getRight(), newState);
					return newState;
				case NOT:
					assert args.length == 1;
					newState = assumeFalse(args[0], newState);
					return newState;
				default:
					logger.warn("assumeTrue: Unknown or unhandled operator " + op.getOperator() + " in assumption " + e);
					return newState;
			}
		} else if (e instanceof RTLBitRange) {
			assert !Options.failFast.getValue() : "Assuming a RTLBitRange is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLConditionalExpression) {
			RTLConditionalExpression c = (RTLConditionalExpression) e;
			RTLExpression cond = c.getCondition();
			RTLExpression negCond = ExpressionFactory.createNot(cond);
			RTLExpression t = c.getTrueExpression();
			RTLExpression f = c.getFalseExpression();
			return assumeTrue(ExpressionFactory.createOr(ExpressionFactory.createAnd(cond, t),ExpressionFactory.createAnd(negCond, f)), newState);
		} else if (e instanceof RTLMemoryLocation) {
			RTLMemoryLocation m = (RTLMemoryLocation) e;
			newState.setMemoryValue(m, TRUE_INTERVAL);
			return newState;
		} else if (e instanceof RTLNondet) {
			// this does not really help, but well...
			return newState;
		} else if (e instanceof RTLNumber) {
			throw new AssertionError("Number did not reduce to a constant: " + e);
		} else if (e instanceof RTLSpecialExpression) {
			assert !Options.failFast.getValue() : "Assuming a RTLSpecialExpression is not really defined, is it?";
			return newState;
		} else if (e instanceof RTLVariable) {
			RTLVariable v = (RTLVariable) e;
			newState.setVariableValue(v, TRUE_INTERVAL);
			return newState;
		} else {
			throw new AssertionError("Unknown assumption " + e);
		}
	}

	public static Set<AbstractState> abstractPost(final RTLStatement statement, final IntervalValuationState s) {
		logger.verbose("start processing abstractPost(" + statement + ") " + statement.getLabel());

		Set<AbstractState> res = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				logger.verbose("Found RTLVariableAssignment: " + stmt);
				IntervalValuationState newState = new IntervalValuationState(s);
				Interval rhs = abstractEval(stmt.getRightHandSide(), s);
				newState.setVariableValue(stmt.getLeftHandSide(), rhs);
				logger.verbose("Assigned " + stmt.getLeftHandSide() + " = " + rhs);
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				logger.verbose("Found RTLMemoryAssignment: " + stmt);
				IntervalValuationState newState = new IntervalValuationState(s);
				Interval rhs = abstractEval(stmt.getRightHandSide(), s);
				newState.setMemoryValue(stmt.getLeftHandSide(), rhs);
				logger.verbose("Written [" + stmt.getLeftHandSide() + "] = " + rhs);
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				logger.verbose("Found RTLAssume: " + stmt);
				RTLExpression e = stmt.getAssumption();
				IntervalValuationState newState = assumeTrue(e, new IntervalValuationState(s));
				return Collections.singleton((AbstractState) newState);
			}

			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				logger.verbose("Ignoring RTLAlloc: " + stmt);
				return Collections.singleton((AbstractState) s);
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				logger.verbose("Ignoring RTLDealloc: " + stmt);
				return Collections.singleton((AbstractState) s);
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				logger.verbose("Found RTLUnknownProcedureCall: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				logger.verbose("Found RTLHavoc: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				logger.verbose("Found RTLMemset: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				logger.verbose("Found RTLMemcpy: " + stmt);
				return Collections.singleton((AbstractState) s); //TODO
			}

			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				logger.verbose("Found RTLStatement: " + stmt);
				assert !Options.failFast.getValue() : "Unknown statement: " + stmt;
				return Collections.singleton((AbstractState)new IntervalValuationState());
			}
		});

		logger.debug("finished abstractPost(" + statement + ") in state: " + s + " with result: " + res);
		return res;
	}


	public static Interval abstractEval(RTLExpression e, final IntervalValuationState s) {
		final Bits bits = Bits.fromInt(e.getBitWidth()); // TODO at least BitRanges explode sometimes...
		ExpressionVisitor<Interval> visitor = new ExpressionVisitor<Interval>() {

			@Override
			public Interval visit(RTLBitRange e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLConditionalExpression e) {
				Interval cond = abstractEval(e.getCondition(), s);
				assert cond.bits == Bits.BIT1 : "Condition has to be a boolean";
				if (!cond.isTop() && cond.minBits.equals(cond.maxBits)) {
					if (cond.minBits.unsafeInternalValue() != 0L) {
						assert cond.minBits.unsafeInternalValue() == 1L;
						return abstractEval(e.getTrueExpression(), s);
					}
					return abstractEval(e.getFalseExpression(), s);
				} else {
					Interval t = abstractEval(e.getTrueExpression(), s);
					Interval f = abstractEval(e.getFalseExpression(), s);
					return t.join(f);
				}
			}

			@Override
			public Interval visit(RTLMemoryLocation m) {
				return s.getMemoryValue(m);
			}

			@Override
			public Interval visit(RTLNondet e) {
				// non-deterministic value, i.e. TOP
				return mkTopInterval(bits);
			}

			@Override
			public Interval visit(RTLNumber e) {
				// a single number, simple
				return mkSomeInterval(e.longValue(), e.longValue(), bits);
			}

			@Override
			public Interval visit(RTLOperation e) {
				RTLExpression[] args = e.getOperands();
				Interval[] iArgs = new Interval[args.length];
				for (int i = 0; i < args.length; i++) {
					iArgs[i] = abstractEval(args[i], s);
				}
				long w = (long)bits.getBitWidth();
				Interval op0, op1, op2;
				switch (e.getOperator()) {
					case UNKNOWN:
						assert !Options.failFast.getValue() : "Evaluated UNKNOWN operator";
						return mkTopInterval(bits);
					case FSIZE:
					case FMUL:
					case FDIV:
					case POWER_OF:
					case ROLC:
					case RORC: /* Rotate with carry */
						// we do not support these operations
						logger.debug("Skipping unsupported operation " + e.getOperator());
						return mkTopInterval(bits);

					// Operators for changing bit-width
					case CAST:
						assert args.length == 2;
						op0 = iArgs[0];
						op1 = iArgs[1];
						if (op1.hasUniqueConcretization()) {
							Bits newBits = Bits.fromInt((int)op1.getUniqueConcretization());
							return op0.truncateInterval(newBits);
						}
						assert false : "CAST called on something crazy";
						return mkTopInterval(bits);
					case SIGN_EXTEND:
					case ZERO_FILL:
						assert e.getOperandCount() == 3 : e.getOperator() + " called with " + e.getOperandCount() + " operands";
						op0 = iArgs[0];
						op1 = iArgs[1];
						op2 = iArgs[2];
						if (op0.hasUniqueConcretization() && op1.hasUniqueConcretization()) {
							switch (e.getOperator()) {
								case SIGN_EXTEND: return op2.signExtendInterval(op0.getUniqueConcretization(), op1.getUniqueConcretization());
								case ZERO_FILL: return op2.zeroExtendInterval(op0.getUniqueConcretization(), op1.getUniqueConcretization());
							}
						}
						assert false : e.getOperator() + " called on something crazy";
						return mkTopInterval(bits);

					// Comparison
					case EQUAL:
						assert args.length == 2;
						op0 = iArgs[0];
						op1 = iArgs[1];
						Interval[] inBoth = op0.intersection(op1);
						if (inBoth.length > 0) {
							if (inBoth.length == 1 && inBoth[0].hasUniqueConcretization()) {
								return TRUE_INTERVAL;
							} else {
								return BOTH_INTERVAL;
							}
						} else {
							return FALSE_INTERVAL;
						}
					case LESS:
					case LESS_OR_EQUAL:
					case UNSIGNED_LESS:
					case UNSIGNED_LESS_OR_EQUAL:
						assert args.length == 2;
						op0 = iArgs[0];
						op1 = iArgs[1];
						return mkTopInterval(bits); //TODO

					// Unary operators
					case NOT:
						assert args.length == 1;
						return iArgs[0].notInterval();
					case NEG:
						assert args.length == 1;
						return iArgs[0].negateInterval();

					// Associative commutative bitwise arithmetic operators
					case AND:
					case OR:
					case XOR:
					case PLUS:
					case MUL:
						assert args.length >= 2;
						op0 = iArgs[0];
						for (int i = 1; i < iArgs.length; i++) {
							op1 = iArgs[i];
							switch (e.getOperator()) {
								case AND:
									op0 = op1.andInterval(op1);
									break;
								case OR:
									op0 = op0.orInterval(op1);
									break;
								case XOR:
									op0 = op0.xorInterval(op1);
									break;
								case PLUS:
									op0 = op0.addInterval(op1);
									break;
								case MUL:
									op0 = op0.mulInterval(op1);
									break;
							}
						}
						return op0;

					// Other bitwise arithmetic operators
					case UDIV:
						assert args.length == 2;
						return iArgs[0].unsignedDivInterval(iArgs[1]);
					case SDIV:
						assert args.length == 2;
						return iArgs[0].signedDivInterval(iArgs[1]);
					case UMOD:
						assert args.length == 2;
						return iArgs[0].unsignedRemInterval(iArgs[1]);
					case SMOD:
						assert args.length == 2;
						return iArgs[0].signedRemInterval(iArgs[1]);

					// Bitwise shift operations
					case SHR:
						assert args.length == 2;
						return iArgs[0].shrInterval(iArgs[1]);
					case SAR:
						assert args.length == 2;
						return iArgs[0].sarInterval(iArgs[1]);
					case SHL:
						assert args.length == 2;
						return iArgs[0].shlInterval(iArgs[1]);
					case ROL:
						// a rol b ==> a shl b | a sar (w - b)
						assert args.length == 2;
						op0 = iArgs[0];
						op1 = iArgs[1];
						op2 = mkSomeInterval(w, w, bits); // w
						return op0.shlInterval(op1).orInterval(op0.sarInterval(op2.subInterval(op1)));
					case ROR:
						// a ror b ==> a sar b | a shl (w - b)
						assert args.length == 2;
						op0 = iArgs[0];
						op1 = iArgs[1];
						op2 = mkSomeInterval(w, w, bits); // w
						return op0.sarInterval(op1).orInterval(op0.shlInterval(op2.subInterval(op1)));
				}
				assert false : "Unknown operator " + e.getOperator();
				return mkTopInterval(bits);
			}

			@Override
			public Interval visit(RTLSpecialExpression e) {
				assert !Options.failFast.getValue() : "Evaluated special expression";
				return mkTopInterval(bits);
			}

			@Override
			public Interval visit(RTLVariable e) {
				return s.getVariableValue(e);
			}
		};

		Interval result = e.accept(visitor);

		logger.debug("abstractEval returned: " + result + " for " + e);

		return result;
	}

	/**
	 * Different kinds of intervals.
	 */
	public enum IntervalKind {
		TOP, INTERVAL, BOT
	}

	private static class BotIntervalIterator implements Iterator<Long> {
		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public Long next() {
			throw new NoSuchElementException("Called next on BOT interval");
		}

		@Override
		public void remove() {
			assert false : "Called remove on BOT interval";
		}
	}
}
