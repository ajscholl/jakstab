package org.jakstab.analysis.signagnostic;

import org.jakstab.JOption;
import org.jakstab.Options;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.signagnostic.abstracted.AbstractDomain;
import org.jakstab.analysis.signagnostic.abstracted.AbstractEvaluator;
import org.jakstab.analysis.signagnostic.abstracted.Boxable;
import org.jakstab.analysis.signagnostic.statistic.Statistic;
import org.jakstab.analysis.signagnostic.utils.BitNumber;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.*;

import java.lang.ref.WeakReference;
import java.math.BigInteger;
import java.util.*;

import static org.jakstab.analysis.signagnostic.utils.BitNumber.bit;
import static org.jakstab.rtl.expressions.RTLBitRange.bitMask;

/**
 * Signedness-agnostic interval implementation. Based on the paper
 * "Interval Analysis and Machine Arithmetic: Why Signedness Ignorance Is Bliss"
 * by
 * GRAEME GANGE, JORGE A. NAVAS, PETER SCHACHTE, HARALD SØNDERGAARD, and PETER J. STUCKEY.
 *
 * Several modifications were performed by A. J. Scholl, described in his bachelor thesis
 * "A Signedness-Agnostic Interval Domain with Congruences and an Implementation for Jakstab"
 *
 * @author A. J. Scholl
 */
final class IntervalElement implements Comparable<IntervalElement>, AbstractDomain<IntervalElement>, Boxable<IntervalElement> {

	/**
	 * Logger.
	 */
	private static final Logger logger = Logger.getLogger(IntervalElement.class);

	/**
	 * Maximum number of numbers to produce before resorting to ALL_NUMBERS when concertizing.
	 */
	private static final JOption<Integer> maxConcretizationSize = JOption.create("interval-concretization-threshold", "k", 20, "Sets the maximum concretization size for intervals.");

	/**
	 * Starting bit pattern. Often denoted a in comments.
	 */
	final BitNumber minBits;

	/**
	 * Ending bit pattern. Often denoted b in comments.
	 */
	final BitNumber maxBits;

	/**
	 * Number of bits for this interval. Often denoted w in comments.
	 */
	private final int bitSize;

	/**
	 * Kind of the interval (top, bot, interval).
	 */
	private final IntervalKind kind;

	/**
	 * Cache for intervals, see {@link BitNumber}.
	 */
	private static final List<Map<IntervalElement, WeakReference<IntervalElement>>> cache = new ArrayList<>(64);

	/**
	 * Cached empty set.
	 */
	private static final IntervalElement[] emptySet = {};

	/**
	 * Cached true value.
	 */
	static final IntervalElement TRUE_INTERVAL = new IntervalElement(BitNumber.TRUE, BitNumber.TRUE, IntervalKind.INTERVAL, false);

	/**
	 * Cached false value.
	 */
	static final IntervalElement FALSE_INTERVAL = new IntervalElement(BitNumber.FALSE, BitNumber.FALSE, IntervalKind.INTERVAL, false);

	/**
	 * Cached TOP for 1-bit intervals (true and false).
	 */
	private static final IntervalElement TRUE_FALSE_INTERVAL = new IntervalElement(1, IntervalKind.TOP);

	static {
		// initialize the cache.
		for (int i = 0; i < 64; i++) {
			cache.add(new HashMap<IntervalElement, WeakReference<IntervalElement>>());
		}
		cache.get(0).put(TRUE_INTERVAL, new WeakReference<>(TRUE_INTERVAL));
		cache.get(0).put(FALSE_INTERVAL, new WeakReference<>(FALSE_INTERVAL));
		cache.get(0).put(TRUE_FALSE_INTERVAL, new WeakReference<>(TRUE_FALSE_INTERVAL));
	}

	/**
	 * Lookup an element in the cache and if it exists, use the reference from the cache.
	 *
	 * @param tmp The element to look up.
	 * @return Something equal to tmp.
	 */
	private static IntervalElement getFromCache(IntervalElement tmp) {
		Statistic.countIntervalElementUse();
		Map<IntervalElement, WeakReference<IntervalElement>> thisCache = cache.get(tmp.bitSize - 1);
		WeakReference<IntervalElement> found = thisCache.get(tmp);
		if (found == null) {
			thisCache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		IntervalElement result = found.get();
		if (result == null) {
			Statistic.countBitNumberUse();
			thisCache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		Statistic.countIntervalElementReuse();
		return result;
	}

	/**
	 * Create a new top or bot interval.
	 *
	 * @param bitSize Number of bits in the interval.
	 * @param kind Kind of the interval, may not be interval.
	 */
	private IntervalElement(int bitSize, IntervalKind kind) {
		assert kind != null;
		assert kind != IntervalKind.INTERVAL;

		minBits = null;
		maxBits = null;
		this.bitSize = bitSize;
		this.kind = kind;
		Statistic.countIntervalElementCreate();
		logger.debug("Created new interval " + this);
	}

	/**
	 * Create a new interval.
	 *
	 * @param minBits First accepted bit pattern. May not be null.
	 * @param maxBits Last accepted bit pattern. May not be null.
	 * @param kind Kind of the interval.
	 * @param allowPromote If true, promote to top if minBits and maxBits span all possible patterns.
	 */
	private IntervalElement(BitNumber minBits, BitNumber maxBits, IntervalKind kind, boolean allowPromote) {
		assert kind != null && minBits != null && maxBits != null;
		assert kind != IntervalKind.INTERVAL || minBits.getBitWidth() == maxBits.getBitWidth();

		bitSize = minBits.getBitWidth();
		if (allowPromote && kind == IntervalKind.INTERVAL && minBits.equals(maxBits.inc())) {
			this.minBits = null;
			this.maxBits = null;
			this.kind = IntervalKind.TOP;
			logger.debug("Promoting (|" + minBits + ", " + maxBits + "|)_" + bitSize + " to TOP");
		} else {
			this.minBits = minBits;
			this.maxBits = maxBits;
			this.kind = kind;
		}
		Statistic.countIntervalElementCreate();
		logger.debug("Created new interval " + this);
	}

	/**
	 * Create a new top interval of the given bitsize.
	 *
	 * @param bitSize The bitsize.
	 * @return The new top interval.
	 */
	public static IntervalElement top(int bitSize) {
		return getFromCache(new IntervalElement(bitSize, IntervalKind.TOP));
	}

	/**
	 * Create a new top interval of the current bitsize.
	 *
	 * @return The new top interval.
	 */
	public IntervalElement top() {
		return top(bitSize);
	}

	/**
	 * Create a new bot interval of the given bitsize.
	 *
	 * @param bitSize The bitsize.
	 * @return The new bot interval.
	 */
	public static IntervalElement bot(int bitSize) {
		return getFromCache(new IntervalElement(bitSize, IntervalKind.BOT));
	}

	/**
	 * Create a new bot interval of the current bitsize.
	 *
	 * @return The new bot interval.
	 */
	public IntervalElement bot() {
		return bot(bitSize);
	}

	/**
	 * Create an interval containing the given number.
	 *
	 * @param num The number.
	 * @param bitSize The bitsize of the number.
	 * @return The interval.
	 */
	public static IntervalElement number(long num, int bitSize) {
		return interval(num, num, bitSize);
	}

	/**
	 * Create an interval containing the given number.
	 *
	 * @param num The number.
	 * @return The interval.
	 */
	public static IntervalElement number(BitNumber num) {
		return interval(num, num);
	}

	/**
	 * Create an interval containing the given number.
	 *
	 * @param num The number.
	 * @return The interval.
	 */
	public static IntervalElement number(RTLNumber num) {
		return number(num.longValue(), num.getBitWidth());
	}

	/**
	 * Create an interval containing the given number using the current bitsize.
	 *
	 * @param num The number.
	 * @return The interval.
	 */
	public IntervalElement number(long num) {
		return number(num, bitSize);
	}

	/**
	 * Create a new interval.
	 *
	 * @param min First allowed number.
	 * @param max Last allowed number.
	 * @param bitSize Bitsize of the numbers.
	 * @return The interval.
	 */
	private static IntervalElement interval(long min, long max, int bitSize) {
		BitNumber minW = BitNumber.valueOf(min, bitSize);
		BitNumber maxW = BitNumber.valueOf(max, bitSize);
		return interval(minW, maxW);
	}


	/**
	 * Create a new interval.
	 *
	 * @param min First allowed number.
	 * @param max Last allowed number.
	 * @return The interval.
	 */
	static IntervalElement interval(BitNumber min, BitNumber max) {
		return getFromCache(new IntervalElement(min, max, IntervalKind.INTERVAL, true));
	}


	/**
	 * Create a new interval using the current bitsize.
	 *
	 * @param min First allowed number.
	 * @param max Last allowed number.
	 * @return The interval.
	 */
	private IntervalElement interval(long min, long max) {
		return interval(min, max, bitSize);
	}


	/**
	 * Create a new interval without promoting to top.
	 *
	 * @param min First allowed number.
	 * @param max Last allowed number.
	 * @return The interval.
	 */
	private static IntervalElement specificInterval(BitNumber min, BitNumber max) {
		return new IntervalElement(min, max, IntervalKind.INTERVAL, false);
	}

	@Override
	public IntervalElement cast(int bitSize) {
		final IntervalElement result;
		if (isTop()) {
			result = top(bitSize);
		} else if (isBot()) {
			result = bot(bitSize);
		} else {
			result = interval(minBits.zExtLongValue(), maxBits.zExtLongValue(), bitSize);
		}
		logger.debug("Casting " + this + " to " + result);
		return result;
	}

	/**
	 * (Unsigned) Maximum number in a non-bottom interval.
	 *
	 * @return Maximum.
	 */
	BitNumber intervalMax() {
		assert !isBot();
		final BitNumber result;
		if (isTop() || maxBits.ult(minBits)) {
			result = BitNumber.uMaxVal(bitSize);
		} else {
			result = maxBits;
		}
		logger.debug("Maximum for " + this + " = " + result);
		return result;
	}


	/**
	 * (Unsigned) Minimum number in a non-bottom interval.
	 *
	 * @return Minimum.
	 */
	BitNumber intervalMin() {
		assert !isBot();
		final BitNumber result;
		if (isTop() || maxBits.ult(minBits)) {
			result = BitNumber.uMinVal(bitSize);
		} else {
			result = minBits;
		}
		logger.debug("Minimum for " + this + " = " + result);
		return result;
	}

	/**
	 * Get the next unsigned lower or equal number for some x in this interval.
	 *
	 * @param x A number.
	 * @return Null if no number <= x exists in the interval, x if x is in the interval or the maximum number smaller than x in the interval.
	 */
	Optional<BitNumber> nextLowerOrEqual(BitNumber x) {
		assert x.getBitWidth() == bitSize;
		final Optional<BitNumber> result;
		if (hasElement(x)) {
			result = new Optional<>(x);
		} else if (!isBot() && x.ugt(maxBits)) {
			result = new Optional<>(maxBits);
		} else {
			result = Optional.none();
		}
		logger.debug("nextLowerOrEqual of " + x + " in " + this + " = " + result);
		return result;
	}

	/**
	 * Get the next unsigned upper or equal number for some x in this interval.
	 *
	 * @param x A number.
	 * @return Null if no number >= x exists in the interval, x if x is in the interval or the minimum number greater than x in the interval.
	 */
	Optional<BitNumber> nextUpperOrEqual(BitNumber x) {
		assert x.getBitWidth() == bitSize;
		final Optional<BitNumber> result;
		if (hasElement(x)) {
			result = new Optional<>(x);
		} else if (!isBot() && x.ult(minBits)) {
			result = new Optional<>(minBits);
		} else {
			result = Optional.none();
		}
		logger.debug("nextUpperOrEqual of " + x + " in " + this + " = " + result);
		return result;
	}

	@Override
	public int compareTo(IntervalElement t) {
		assertCompatible(t);
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
		if (o != null && o.getClass() == getClass()) {
			IntervalElement t = (IntervalElement) o;
			return bitSize == t.bitSize && compareTo(t) == 0;
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		return kind.hashCode() ^ bitSize ^ (kind == IntervalKind.INTERVAL ? minBits.hashCode() ^ maxBits.hashCode() : 0);
	}

	@Override
	public String toString() {
		return getIdentifier();
	}

	@Override
	public int getBitWidth() {
		return bitSize;
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
		int i = 0;
		for (BitNumber l : this) {
			i++;
			if (i > 100) {
				return RTLNumber.ALL_NUMBERS;
			}
			s.add(ExpressionFactory.createNumber(l.sExtLongValue(), bitSize));
		}
		return s;
	}

	@Override
	public IntervalElement abstractGet() {
		return this;
	}

	@Override
	public AbstractDomain<IntervalElement> abstractBox() {
		return this;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !isTop() && !isBot() && minBits.equals(maxBits);
	}

	@Override
	public BitNumber getUniqueConcretization() {
		assert hasUniqueConcretization();
		return minBits;
	}

	@Override
	public IntervalElement join(LatticeElement l) {
		IntervalElement t = (IntervalElement) l;
		assertCompatible(t);
		final IntervalElement result;
		if (lessOrEqual(t)) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (t.hasElement(minBits) && t.hasElement(maxBits) && hasElement(t.minBits) && hasElement(t.maxBits)) {
			result = top();
		} else if (t.hasElement(maxBits) && hasElement(t.minBits)) {
			result = interval(minBits, t.maxBits);
		} else if (hasElement(t.maxBits) && t.hasElement(minBits)) {
			result = interval(t.minBits, maxBits);
		} else {
			BigInteger r1 = internalSize(maxBits, t.minBits);
			BigInteger r2 = internalSize(t.maxBits, minBits);
			int cmp = r1.compareTo(r2);
			if (cmp < 0 || cmp == 0 && minBits.ult(t.minBits)) {
				result = interval(minBits, t.maxBits);
			} else {
				result = interval(t.minBits, maxBits);
			}
		}
		logger.debug("Joining " + this + " and " + t + " to " + result);
		assert lessOrEqual(result) && t.lessOrEqual(result) : "join returned something which is not greater or equal";
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		IntervalElement t = (IntervalElement) l;
		return isSubIntervalOf(t);
	}

	@Override
	public boolean isTop() {
		return kind == IntervalKind.TOP;
	}

	@Override
	public boolean isBot() {
		return kind == IntervalKind.BOT;
	}

	/**
	 * Check if the interval is not top or bot.
	 *
	 * @return True if the interval is really an interval.
	 */
	public boolean isInterval() {
		return kind == IntervalKind.INTERVAL;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return new GenericValuationState<>(IntervalElementFactory.getFactory()).projectionFromConcretization(expressions);
	}

	public static Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<IntervalElement> s) {
		logger.info("projection from concretization for " + expressions.length + " expressions: " + Arrays.toString(expressions) + " with evaluator " + s);
		Tuple<Set<RTLNumber>> cValues = new Tuple<>(expressions.length);
		for (int i = 0; i < expressions.length; i++) {
			IntervalElement aValue = s.evalExpression(expressions[i]).abstractGet();
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
				for (BitNumber l : aValue) {
					k++;
					if (k > maxConcretizationSize.getValue()) {
						logger.warn("limiting " + aValue + " with " + aValue.size() + " elements to " + maxConcretizationSize.getValue() + " elements");
						tmp = RTLNumber.ALL_NUMBERS;
						break;
					} else {
						tmp.add(ExpressionFactory.createNumber(l.sExtLongValue(), aValue.bitSize));
					}
				}
				cValues.set(i, tmp);
			}
		}
		Set<Tuple<RTLNumber>> result = Sets.crossProduct(cValues);
		logger.info("Projected " + result);
		return result;
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(getClass().getSimpleName() + " does not contain location information.");
	}

	@Override
	public String getIdentifier() {
		if (isTop()) {
			return "TOP_" + bitSize;
		} else if (isBot()) {
			return "BOT_" + bitSize;
		} else {
			return "(|" + minBits + ", " + maxBits + "|)_" + bitSize;
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
			size = maxIntervalSize();
		} else if (isBot()) {
			size = BigInteger.ZERO;
		} else {
			size = internalSize(minBits, maxBits);
		}
		logger.debug("Size of " + this + " is " + size);
		return size;
	}

	/**
	 * Get the maximum possible size of the interval, 2^w.
	 *
	 * @return 2^w
	 */
	BigInteger maxIntervalSize() {
		return maxIntervalSize(bitSize);
	}

	/**
	 * Get the maximum possible size of the interval, 2^w.
	 *
	 * @return 2^w
	 */
	static BigInteger maxIntervalSize(int bitSize) {
		return BigInteger.valueOf(2L).pow(bitSize);
	}

	private static BigInteger internalSize(BitNumber min, BitNumber max) {
		return max.sub(min).inc().unsignedBigValue();
	}

	/**
	 * Invert this interval.
	 *
	 * @return Inverted interval.
	 */
	IntervalElement invert() {
		final IntervalElement result;
		if (isBot()) {
			result = top();
		} else if (isTop()) {
			result = bot();
		} else {
			result = interval(maxBits.inc(), minBits.dec());
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
	private boolean hasElement(long e) {
		long fitted = BitNumber.valueOf(e, bitSize).sExtLongValue();
		assert e == fitted : "bad call to hasElement with " + e + " (" + fitted + ", " + bitSize + ')';
		return hasElement(BitNumber.valueOf(e, bitSize));
	}

	@Override
	public boolean hasElement(RTLNumber e) {
		assert bitSize == e.getBitWidth() : "Wrong bit-size. Got " + e.getBitWidth() + ", but expected " + bitSize;
		return hasElement(e.longValue());
	}

	@Override
	public boolean hasElement(BitNumber e) {
		assert e.getBitWidth() == bitSize;
		boolean result = isTop() || !isBot() && minBits.relativeLeq(e, maxBits);
		logger.debug(e + " element of " + this + ": " + result);
		if (hasUniqueConcretization()) {
			if (e.equals(getUniqueConcretization()) != result ) {
				logger.debug(isTop());
				logger.debug(isBot());
				logger.debug(minBits.relativeLeq(e, maxBits));
			}
			assert e.equals(getUniqueConcretization()) == result : "hasElement for single-element interval broken for " + this + " and " + e;
		}
		return result;
	}

	/**
	 * Assert that the given interval is compatible with the current one.
	 *
	 * @param t The interval to check.
	 */
	void assertCompatible(IntervalElement t) {
		assert t != null;
		assert bitSize == t.bitSize : "Incompatible intervals: " + this + " and " + t;
	}

	/**
	 * Check if this interval is a sub-interval of another interval.
	 *
	 * @param t The interval to check.
	 * @return True if the interval is a sub-interval.
	 */
	private boolean isSubIntervalOf(IntervalElement t) {
		assertCompatible(t);
		boolean result = isBot() || // bot is always a sub interval
				t.isTop() || // everything is a sub interval of top
				!(isTop() || t.isBot()) && // top is not a sub interval of something other than top
						t.hasElement(minBits) && t.hasElement(maxBits) && // both ends should lie in the other interval
						(equals(t) || !hasElement(t.minBits) || !hasElement(t.maxBits)); // one end of the other interval
																						 // should not be in this interval
																						 // or both intervals should be equal
		logger.debug(this + " is a subset of " + t + ": " + result);
		return result;
	}

	/**
	 * Compute the greatest lower bound of two values.
	 *
	 * @param t The other value.
	 * @return The greatest lower bound.
	 */
	@Override
	public IntervalElement meet(IntervalElement t) {
		return joins(bitSize, Arrays.asList(intersection(t)));
	}

	/**
	 * Compute the gap between two intervals.
	 *
	 * @param t The other interval.
	 * @return The gap between both intervals.
	 */
	private IntervalElement gap(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement result;
		if (kind == IntervalKind.INTERVAL && t.kind == IntervalKind.INTERVAL && !t.hasElement(maxBits) && !hasElement(t.minBits)) {
			result = interval(t.minBits, maxBits).invert();
		} else {
			result = bot();
		}
		logger.debug("Gap between " + this + " and " + t + " = " + result);
		assert intersection(result).length == 0;
		assert t.intersection(result).length == 0;
		return result;
	}

	/**
	 * Construct an interval containing this and the given interval.
	 *
	 * @param t The other interval.
	 * @return An interval containing both.
	 */
	private IntervalElement extend(IntervalElement t) {
		// the definitions of extend in the paper all have problems, just use join
		return join(t);
	}

	/**
	 * Return the smaller of two intervals.
	 *
	 * @param s The first interval.
	 * @param t The second interval.
	 * @return The smaller interval.
	 */
	static IntervalElement smaller(IntervalElement s, IntervalElement t) {
		s.assertCompatible(t);
		IntervalElement result = t.size().compareTo(s.size()) > 0 ? s : t;
		logger.debug("Smaller of " + s + " and " + t + " = " + result);
		return result;
	}

	/**
	 * Return the bigger of two intervals.
	 *
	 * @param s The first interval.
	 * @param t The second interval.
	 * @return The bigger interval.
	 */
	static IntervalElement bigger(IntervalElement s, IntervalElement t) {
		s.assertCompatible(t);
		IntervalElement result = t.size().compareTo(s.size()) > 0 ? t : s;
		logger.debug("Bigger of " + s + " and " + t + " = " + result);
		return result;
	}

	/**
	 * Compute the least upper bound of a set of intervals.
	 *
	 * @param bitSize Bit size of the arguments (for empty sets).
	 * @param c A set of intervals.
	 * @return The least upper bound.
	 */
	static IntervalElement joins(int bitSize, Collection<IntervalElement> c) {
		List<IntervalElement> s = new ArrayList<>(c.size());
		for (IntervalElement e : c) {
			assert e.getBitWidth() == bitSize;
			s.add(e);
		}
		Collections.sort(s);
		logger.debug("** starting joins of " + s);
		IntervalElement f = bot(bitSize);
		IntervalElement g = f;
		for (IntervalElement e : s) {
			if (e.isTop() || e.kind == IntervalKind.INTERVAL && e.maxBits.ult(e.minBits)) {
				f = f.extend(e);
			}
		}
		for (IntervalElement e : s) {
			g = bigger(g, f.gap(e));
			f = f.extend(e);
		}
		IntervalElement result = bigger(f.invert(), g).invert();
		logger.debug("Joins of " + s + " = " + result);
		for (IntervalElement e : s) {
			assert e.lessOrEqual(result) : "Element " + e + " should be in interval " + result + ", but wasn't.";
		}
		return result;
	}

	@Override
	public AbstractDomain<IntervalElement> joins(Collection<IntervalElement> c) {
		return joins(bitSize, c);
	}

	/**
	 * Compute the intersection of two intervals.
	 *
	 * @param t The other intervals.
	 * @return All sub-intervals in both intervals.
	 */
	IntervalElement[] intersection(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement[] result;
		if (isBot() || t.isBot()) {
			result = emptySet;
		} else if (equals(t) || isTop()) {
			result = new IntervalElement[]{t};
		} else if (t.isTop()) {
			result = new IntervalElement[]{this};
		} else {
			boolean minInT = t.hasElement(minBits);
			boolean maxInT = t.hasElement(maxBits);
			boolean tMinInThis = hasElement(t.minBits);
			boolean tMaxInThis = hasElement(t.maxBits);
			if (minInT && maxInT && tMinInThis && tMaxInThis) {
				result = new IntervalElement[]{interval(minBits, t.maxBits), interval(t.minBits, maxBits)};
			} else if (minInT && maxInT) {
				result = new IntervalElement[]{this};
			} else if (tMinInThis && tMaxInThis) {
				result = new IntervalElement[]{t};
			} else if (minInT && tMaxInThis) {
				result = new IntervalElement[]{interval(minBits, t.maxBits)};
			} else if (maxInT && tMinInThis) {
				result = new IntervalElement[]{interval(t.minBits, maxBits)};
			} else {
				result = emptySet;
			}
		}
		logger.debug("Intersection of " + this + " and " + t + " = " + Arrays.toString(result));
		for (IntervalElement e : result) {
			assert e.lessOrEqual(this) : "intersection returned something not in this interval";
			assert e.lessOrEqual(t) : "intersection returned something not in the other interval";
		}
		return result;
	}

	@Override
	public IntervalElement add(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement result;
		if (isBot() || t.isBot()) {
			result = bot();
		} else if (size().add(t.size()).compareTo(maxIntervalSize()) <= 0) {
			result = interval(minBits.add(t.minBits), maxBits.add(t.maxBits));
		} else {
			result = top();
		}
		logger.debug(this + " + " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement sub(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement result;
		if (isBot() || t.isBot()) {
			result = bot();
		} else if (size().add(t.size()).compareTo(maxIntervalSize()) <= 0) {
			result = interval(minBits.sub(t.maxBits), maxBits.sub(t.minBits));
		} else {
			result = top();
		}
		logger.debug(this + " - " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement negate() {
		IntervalElement result = number(0L).sub(this);
		logger.debug("-" + this + " = " + result);
		return result;
	}

	/**
	 * Get the start of the north pole.
	 *
	 * @return The start of the north pole.
	 */
	BitNumber northPoleStart() {
		return northPoleEnd().not();
	}

	/**
	 * Get the end of the north pole.
	 *
	 * @return The end of the north pole.
	 */
	BitNumber northPoleEnd() {
		return BitNumber.valueOf(1L << (long)(bitSize - 1), bitSize);
	}

	/**
	 * Get the start of the south pole.
	 *
	 * @return The start of the south pole.
	 */
	BitNumber southPoleStart() {
		return southPoleEnd().not();
	}

	/**
	 * Get the end of the south pole.
	 *
	 * @return The end of the south pole.
	 */
	BitNumber southPoleEnd() {
		return BitNumber.valueOf(0L, bitSize);
	}

	/**
	 * Get the north pole.
	 *
	 * @return The north pole.
	 */
	private IntervalElement northPole() {
		return interval(northPoleStart(), northPoleEnd());
	}

	/**
	 * Get the south pole.
	 *
	 * @return The south pole.
	 */
	private IntervalElement southPole() {
		return interval(southPoleStart(), southPoleEnd());
	}

	/**
	 * Split an interval at the north pole.
	 *
	 * @return All sub-intervals.
	 */
	private IntervalElement[] splitNorth() {
		final IntervalElement[] result;
		if (isBot()) {
			result = emptySet;
		} else if (isTop()) {
			result = new IntervalElement[]{interval(southPoleEnd(), northPoleStart()), interval(northPoleEnd(), southPoleStart())};
		} else if (!northPole().isSubIntervalOf(this)) {
			result = new IntervalElement[]{this};
		} else {
			result = new IntervalElement[]{interval(minBits, northPoleStart()), interval(northPoleEnd(), maxBits)};
		}
		logger.debug("Splitting " + this + " at the north pole = " + Arrays.toString(result));
		return result;
	}

	/**
	 * Split an interval at the south pole.
	 *
	 * @return All sub-intervals.
	 */
	IntervalElement[] splitSouth() {
		final IntervalElement[] result;
		if (isBot()) {
			result = emptySet;
		} else if (isTop()) {
			result = new IntervalElement[]{interval(northPoleEnd(), southPoleStart()), interval(southPoleEnd(), northPoleStart())};
		} else if (!southPole().isSubIntervalOf(this)) {
			result = new IntervalElement[]{this};
		} else {
			result = new IntervalElement[]{interval(southPoleEnd(), maxBits), interval(minBits, southPoleStart())};
		}
		logger.debug("Splitting " + this + " at the south pole = " + Arrays.toString(result));
		return result;
	}

	/**
	 * Split an interval at the north and south pole.
	 *
	 * @return All sub-intervals.
	 */
	Set<IntervalElement> cut() {
		Set<IntervalElement> result = new FastSet<>();
		for (IntervalElement u : splitNorth()) {
			Collections.addAll(result, u.splitSouth());
		}
		logger.debug("Cutting " + this + " = " + result);
		return result;
	}

	/**
	 * Unsigned multiply two intervals (may not be top or bot).
	 *
	 * @param t The other interval.
	 * @return The resulting interval.
	 */
	private IntervalElement mul_u(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL && t.kind == IntervalKind.INTERVAL;
		final IntervalElement result;
		if (!minBits.uMulOverflow(t.minBits) && !maxBits.uMulOverflow(t.maxBits)) {
			result = interval(minBits.mul(t.minBits), maxBits.mul(t.maxBits));
		} else {
			result = top();
		}
		logger.debug(this + " x_u " + t + " = " + result);
		return result;
	}

	/**
	 * Signed multiply two intervals (may not be top or bot).
	 *
	 * @param t The other interval.
	 * @return The resulting interval.
	 */
	private IntervalElement mul_s(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL && t.kind == IntervalKind.INTERVAL;
		boolean a_msb = minBits.msb();
		boolean b_msb = maxBits.msb();
		boolean c_msb = t.minBits.msb();
		boolean d_msb = t.maxBits.msb();
		boolean ac_no_ov = !minBits.sMulOverflow(t.minBits);
		boolean bd_no_ov = !maxBits.sMulOverflow(t.maxBits);
		boolean ad_no_ov = !minBits.sMulOverflow(t.maxBits);
		boolean bc_no_ov = !maxBits.sMulOverflow(t.minBits);
		final IntervalElement result;
		if (!a_msb && !b_msb && !c_msb && !d_msb && ac_no_ov && bd_no_ov) {
			result = interval(minBits.mul(t.minBits), maxBits.mul(t.maxBits));
		} else if (a_msb && b_msb && c_msb && d_msb && ac_no_ov && bd_no_ov) {
			result = interval(maxBits.mul(t.maxBits), minBits.mul(t.minBits));
		} else if (a_msb && b_msb && !c_msb && !d_msb && ad_no_ov && bc_no_ov) {
			result = interval(minBits.mul(t.maxBits), maxBits.mul(t.minBits));
		} else if (!a_msb && !b_msb && c_msb && d_msb && ad_no_ov && bc_no_ov) {
			result = interval(maxBits.mul(t.minBits), minBits.mul(t.maxBits));
		} else {
			result = top();
		}
		logger.debug(this + " x_s " + t + " = " + result);
		return result;
	}

	/**
	 * Signed and unsigned multiply two intervals (may not be top or bot).
	 *
	 * @param t The other interval.
	 * @return The resulting intervals.
	 */
	private IntervalElement[] mul_us(IntervalElement t) {
		IntervalElement[] result = mul_u(t).intersection(mul_s(t));
		logger.debug(this + " x_us " + t + " = " + Arrays.toString(result));
		return result;
	}

	/**
	 * Double the bitsize of an interval (for multiplication).
	 *
	 * @return An interval with twice the bitsize.
	 */
	private IntervalElement extentBitSize() {
		switch (bitSize) {
			case 1:
				assert !Options.failFast.getValue() : "Extending 1-bit interval";
				logger.warn("Extending 1-bit interval!");
			case 8:
			case 16:
			case 32:
				return cast(bitSize * 2);
			case 64:
				return this;
			default:
				assert !Options.failFast.getValue() : "Extending " + bitSize + "-bit interval";
				logger.warn("Extending " + bitSize + "-bit interval!");
				return cast(Math.min(64, bitSize * 2));
		}
	}

	@Override
	public IntervalElement mulDouble(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> s = new FastSet<>();
		for (IntervalElement u : cut()) {
			// extend the parts to double the bitsize. Jakstab models multiplication as doubling the bitsize, so we better do so too.
			IntervalElement us = u.extentBitSize();
			for (IntervalElement v : t.cut()) {
				Collections.addAll(s, us.mul_us(v.extentBitSize()));
			}
		}
		IntervalElement result = joins(extentBitSize().bitSize, s);
		logger.debug(this + " *d " + t + " = " + result);
		return result;
	}

	/**
	 * Plain multiplication operator which does not double the bit-width.
	 *
	 * @param t The other interval.
	 * @return The result.
	 */
	public IntervalElement mul(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> s = new FastSet<>();
		for (IntervalElement u : cut()) {
			for (IntervalElement v : t.cut()) {
				Collections.addAll(s, u.mul_us(v));
			}
		}
		IntervalElement result = joins(bitSize, s);
		logger.debug(this + " * " + t + " = " + result);
		return result;
	}

	/**
	 * Take the join of the intersection of two intervals.
	 *
	 * @param t The other interval.
	 * @return An interval containing only things in both intervals.
	 */
	IntervalElement joinIntersections(IntervalElement t) {
		Collection<IntervalElement> s = new FastSet<>();
		Collections.addAll(s, intersection(t));
		return joins(bitSize, s);
	}

	/**
	 * Remove an interval from an interval.
	 *
	 * @param t The interval to remove.
	 * @return The result.
	 */
	private IntervalElement difference(IntervalElement t) {
		return joinIntersections(t.invert());
	}

	/**
	 * Remove the (|0, 0|) interval from the border of an interval.
	 *
	 * @return The interval without 0.
	 */
	private IntervalElement removeZero() {
		return difference(number(0L));
	}

	/**
	 * Unsigned division worker function.
	 *
	 * @param t The other interval, may not be top or bot or include 0 as a bound.
	 * @return The result of the division.
	 */
	private IntervalElement div_u(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		IntervalElement result = interval(minBits.uquot(t.maxBits), maxBits.uquot(t.minBits));
		logger.debug(this + " /_u " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement unsignedDiv(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				results.add(u.div_u(v.removeZero()));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " /u " + t + " = " + result);
		return result;
	}


	/**
	 * Signed division worker function.
	 *
	 * @param t The other interval, may not be top or bot or include 0 as a bound.
	 * @return The result of the division.
	 */
	private IntervalElement div_s(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final IntervalElement result;
		boolean msb1 = minBits.msb();
		boolean msb2 = t.minBits.msb();
		// signed division with -1 is sometimes undefined if the first argument is sMinBound, sometimes not
		// x86 defines this as an error, so we map this to bot. java on the other side defines it as sMinBound,
		// so one has to be careful about the interpretation one chooses.
		if (t.minBits.sExtLongValue() == -1L || t.maxBits.sExtLongValue() == -1L) {
			// Compute result without -1 in the second operand.
			IntervalElement r1 = div_s(t.difference(number(-1L)));
			// Compute result with -1 as second operand and without sMinBound as the first operand.
			IntervalElement r2 = difference(number(minBits.sMinVal())).div_s(number(-1L));
			// join both parts.
			result = r1.join(r2);
		} else if (!msb1 && !msb2) {
			result = interval(minBits.squot(t.maxBits), maxBits.squot(t.minBits));
		} else if (msb1 && msb2) {
			result = interval(maxBits.squot(t.minBits), minBits.squot(t.maxBits));
		} else if (!msb1) {
			result = interval(maxBits.squot(t.maxBits), minBits.squot(t.minBits));
		} else {
			result = interval(minBits.squot(t.minBits), maxBits.squot(t.maxBits));
		}
		logger.debug(this + " /_s " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement signedDiv(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : cut()) {
			for (IntervalElement v : t.cut()) {
				results.add(u.div_s(v.removeZero()));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " /s " + t + " = " + result);
		return result;
	}

	/**
	 * Create a maximal ambiguous result for a remainder operation.
	 *
	 * @return The result.
	 */
	private IntervalElement amb() {
		assert kind == IntervalKind.INTERVAL;
		return interval(minBits.valueOf(0L), maxBits.dec());
	}

	/**
	 * Unsigned remainder using a modulus join.
	 *
	 * @param t Number to divide by.
	 * @return An interval consisting of as few as possible values between 0 and t - 1, all being possible remainders
	 * 		   after dividing by t.
	 */
	IntervalElement num_rem_cc(BitNumber t) {
		return joinsMod(t, num_rem_w(t));
	}

	/**
	 * Exact unsigned remainder function. Returns a list of possible result arrays.
	 *
	 * @param r The number to take the remainder of.
	 * @return A list containing possible intervals for the remainder.
	 */
	List<IntervalElement> num_rem_w(BitNumber r) {
		assert bitSize == r.getBitWidth();
		assert r.zExtLongValue() != 0L;
		final List<IntervalElement> result;
		if (r.zExtLongValue() == 0L) {
			result = Collections.emptyList();
		} else {
			result = new ArrayList<>();
			for (IntervalElement a : splitSouth()) {
				assert a.kind == IntervalKind.INTERVAL;
				if (a.maxBits.sub(a.minBits).ult(r)) {
					BitNumber newMin = a.minBits.urem(r);
					BitNumber newMax = a.maxBits.urem(r);
					BitNumber base = a.maxBits.sub(newMax);
					if (a.minBits.ult(base)) {
						result.add(interval(newMin, r.dec()));
						result.add(interval(a.minBits.valueOf(0L), newMax));
					} else {
						result.add(interval(newMin, newMax));
					}
				} else {
					result.add(interval(a.minBits.valueOf(0L), r.dec()));
				}
			}
		}
		logger.debug("Unsigned remainder set of " + this + " and " + r + " = " + result);
		return result;
	}

	/**
	 * Unsigned remainder of an interval and a single number. The number may not be zero.
	 *
	 * @param r The number to take the remainder of.
	 * @return The resulting interval.
	 */
	private IntervalElement num_rem(BitNumber r) {
		IntervalElement result = joins(bitSize, num_rem_w(r));
		logger.debug("Unsigned remainder of " + this + " and " + r + " = " + result);
		return result;
	}

	/**
	 * Unsigned remainder of two intervals. Both should not be top or bot and should not include zero.
	 *
	 * @param t The other interval.
	 * @return The resulting interval.
	 */
	private IntervalElement rem_u(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final IntervalElement result;
		IntervalElement divided = div_u(t);
		if (divided.size().equals(BigInteger.ONE)) {
			result = sub(divided).mul(t);
		} else {
			if (t.hasUniqueConcretization()) {
				result = num_rem(t.getUniqueConcretization());
			} else {
				result = t.amb();
			}
		}
		logger.debug(this + " %_u " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement unsignedRem(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				results.add(u.rem_u(v.removeZero()));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " %u " + t + " = " + result);
		return result;
	}

	/**
	 * Signed remainder of two intervals. Both should not be top or bot and should not include zero.
	 *
	 * @param t The other interval.
	 * @return The resulting interval.
	 */
	private IntervalElement rem_s(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		final IntervalElement result;
		IntervalElement divided = div_s(t);
		if (divided.size().equals(BigInteger.ONE)) {
			result = sub(divided).mul(t);
		} else {
			assert minBits.sign().equals(maxBits.sign()) : "Signs do not equal";
			assert t.minBits.sign().equals(t.maxBits.sign()) : "Signs do not equal";
			BitNumber thisSign = minBits.sign();
			BitNumber tSign = t.minBits.sign();
			result = number(thisSign).mul(number(tSign).mul(t).amb());
		}
		logger.debug(this + " %_s " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement signedRem(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		// take the cut instead of splitting at the south pole as the sign counts!
		// this is just similar to signed division.
		for (IntervalElement u : cut()) {
			for (IntervalElement v : t.cut()) {
				results.add(u.rem_s(v.removeZero()));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " %s " + t + " = " + result);
		return result;
	}

	/**
	 * Compute the minimum bound of the bitwise or of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New minimum.
	 */
	private BitNumber minOr(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		assert a.getBitWidth() == b.getBitWidth();
		assert a.getBitWidth() == c.getBitWidth();
		assert a.getBitWidth() == d.getBitWidth();
		assert a.getBitWidth() == bitSize;
		BitNumber m = northPoleEnd().shr(a.xor(c).numberOfLeadingZeros());
		while (m.zExtLongValue() != 0L) {
			if (a.not().and(c).and(m).zExtLongValue() != 0L) {
				BitNumber e = a.or(m).and(m.negate());
				if (e.uleq(b)) {
					return e.or(c);
				}
			} else if (a.and(c.not()).and(m).zExtLongValue() != 0L) {
				BitNumber e = c.or(m).and(m.negate());
				if (e.uleq(d)) {
					return a.or(e);
				}
			}
			m = m.shr(1);
		}
		return a.or(c);
	}

	/**
	 * Compute the maximum bound of the bitwise or of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New maximum.
	 */
	private BitNumber maxOr(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		assert a.getBitWidth() == b.getBitWidth();
		assert a.getBitWidth() == c.getBitWidth();
		assert a.getBitWidth() == d.getBitWidth();
		assert a.getBitWidth() == bitSize;
		BitNumber m = northPoleEnd().shr(b.and(d).numberOfLeadingZeros());
		while (m.zExtLongValue() != 0L) {
			if (b.and(d).and(m).zExtLongValue() != 0L) {
				BitNumber e = b.sub(m).or(m.dec());
				if (e.ugeq(a)) {
					return e.or(d);
				}
				BitNumber f = d.sub(m).or(m.dec());
				if (f.ugeq(c)) {
					return b.or(f);
				}
			}
			m = m.shr(1);
		}
		return b.or(d);
	}

	/**
	 * Compute the bitwise or of two intervals (both not crossing the south pole or being bot).
	 *
	 * @param t The other interval.
	 * @return The result.
	 */
	private IntervalElement orW(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		BitNumber min = minOr(minBits, maxBits, t.minBits, t.maxBits);
		BitNumber max = maxOr(minBits, maxBits, t.minBits, t.maxBits);
		IntervalElement result = interval(min, max);
		logger.debug(this + " |w " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement or(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				results.add(u.orW(v));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " | " + t + " = " + result);
		return result;
	}

	/**
	 * Compute the minimum bound of the bitwise and of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New minimum.
	 */
	private BitNumber minAnd(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		return maxOr(b.not(), a.not(), d.not(), c.not()).not();
	}

	/**
	 * Compute the maximum bound of the bitwise and of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New maximum.
	 */
	private BitNumber maxAnd(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		return minOr(b.not(), a.not(), d.not(), c.not()).not();
	}

	/**
	 * Compute the bitwise and of two intervals (both not crossing the south pole or being bot).
	 *
	 * @param t The other interval.
	 * @return The result.
	 */
	private IntervalElement andW(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		BitNumber min = minAnd(minBits, maxBits, t.minBits, t.maxBits);
		BitNumber max = maxAnd(minBits, maxBits, t.minBits, t.maxBits);
		IntervalElement result = interval(min, max);
		logger.debug(this + " &w " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement and(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				results.add(u.andW(v));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " & " + t + " = " + result);
		return result;
	}

	/**
	 * Compute the minimum bound of the bitwise xor of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New minimum.
	 */
	private BitNumber minXor(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		return minAnd(a, b, d.not(), c.not()).or(minAnd(b.not(), a.not(), c, d));
	}

	/**
	 * Compute the maximum bound of the bitwise xor of two intervals [a, b] and [c, d].
	 *
	 * @param a First minimum.
	 * @param b First maximum.
	 * @param c Second minimum.
	 * @param d Second maximum.
	 * @return New maximum.
	 */
	private BitNumber maxXor(BitNumber a, BitNumber b, BitNumber c, BitNumber d) {
		BitNumber z = a.valueOf(0L);
		return maxOr(z, maxAnd(a, b, d.not(), c.not()), z, maxAnd(b.not(), a.not(), c, d));
	}

	/**
	 * Compute the bitwise xor of two intervals (both not crossing the south pole or being bot).
	 *
	 * @param t The other interval.
	 * @return The result.
	 */
	private IntervalElement xorW(IntervalElement t) {
		assertCompatible(t);
		assert kind == IntervalKind.INTERVAL;
		assert t.kind == IntervalKind.INTERVAL;
		BitNumber min = minXor(minBits, maxBits, t.minBits, t.maxBits);
		BitNumber max = maxXor(minBits, maxBits, t.minBits, t.maxBits);
		IntervalElement result = interval(min, max);
		logger.debug(this + " ^w " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement xor(IntervalElement t) {
		assertCompatible(t);
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				results.add(u.xorW(v));
			}
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " ^ " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement not() {
		IntervalElement result = add(number(1L)).negate();
		logger.debug("~" + this + " = " + result);
		return result;
	}

	@Override
	public IntervalElement signExtend(int firstBit, int lastBit) {
		assert firstBit > 0 && firstBit <= 64 && firstBit <= lastBit : "Invalid first bit " + firstBit;
		assert lastBit > 0 && lastBit <= 64 : "Invalid last bit " + lastBit;
		int targetWidth = Math.max(bitSize, lastBit + 1);
		IntervalElement result = signExtend(targetWidth);
		if (firstBit - 1 == bitSize) {
			return result;
		} else {
			// this looks kinda fishy... so lets fail for the moment, remove the assert if this is a valid case...
			// this actually is a valid case...
			//assert false : "Strange sign extension: " + firstBit + " to " + lastBit + " for " + this;
			if (result.kind == IntervalKind.INTERVAL) {
				// create the result if the msb is sign-extended to firstBit:lastBit.
				IntervalElement sRes = result.or(number(bitMask(firstBit, lastBit), targetWidth));
				if (result.minBits.msb() && result.maxBits.msb()) {
					// sign bit is always present
					return sRes;
				} else if (!result.minBits.msb() && !result.maxBits.msb()) {
					// sign bit is never present
					// wrap around is not an issue here as the complete signed
					// half is included anyway if a sign bit could exist
					return result;
				} else {
					// sign bit may be present
					return result.join(sRes);
				}
			} else {
				return result; // top or bot
			}
		}
	}

	@Override
	public IntervalElement signExtend(int bitSize) {
		assert bitSize >= this.bitSize;
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement i : splitNorth()) {
			assert i.kind == IntervalKind.INTERVAL;
			results.add(interval(i.minBits.sExtend(bitSize), i.maxBits.sExtend(bitSize)));
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " `signExtend` " + bitSize + " = " + result);
		return result;
	}

	@Override
	public IntervalElement zeroExtend(int firstBit, int lastBit) {
		assert firstBit > 0 && firstBit <= 64 && firstBit <= lastBit : "Invalid first bit " + firstBit;
		assert lastBit > 0 && lastBit <= 64 : "Invalid last bit " + lastBit;
		int targetWidth = Math.max(bitSize, lastBit + 1);
		IntervalElement result = zeroExtend(targetWidth);
		if (firstBit - 1 == bitSize) {
			return result;
		} else {
			// keep only the bits from 0..firstBit-1 and lastBit+1 .. targetWidth-1, as the other bits
			// should get set to 0 from the extension.
			return result.and(number(bitMask(0, firstBit - 1) | bitMask(lastBit + 1, targetWidth - 1), targetWidth));
		}
	}

	@Override
	public IntervalElement zeroExtend(int bitSize) {
		assert bitSize >= this.bitSize;
		Set<IntervalElement> results = new FastSet<>();
		for (IntervalElement i : splitSouth()) {
			assert i.kind == IntervalKind.INTERVAL;
			results.add(interval(i.minBits.zExtend(bitSize), i.maxBits.zExtend(bitSize)));
		}
		IntervalElement result = joins(bitSize, results);
		logger.debug(this + " `zeroExtend` " + bitSize + " = " + result);
		return result;
	}

	@Override
	public IntervalElement truncate(int bitSize) {
		logger.debug("Truncating " + this + " to " + bitSize);
		assert bitSize <= this.bitSize;
		final IntervalElement result;
		if (isBot()) {
			result = bot(bitSize);
		} else if (isTop()) {
			result = top(bitSize);
		} else {
			BitNumber mask = BitNumber.valueOf(bit(bitSize - 1) - 1L, this.bitSize);
			BitNumber a = minBits.shr(bitSize);
			BitNumber b = maxBits.shr(bitSize);
			BitNumber tMin = minBits.and(mask);
			BitNumber tMax = maxBits.and(mask);
			BitNumber x = tMin.trunc(bitSize);
			BitNumber y = tMax.trunc(bitSize);
			if (a.equals(b) && tMin.uleq(tMax)) {
				result = interval(x, y);
			} else {
				a = a.inc();
				if (a.equals(b) && tMin.ugt(tMax)) {
					result = interval(x, y);
				} else {
					result = top(bitSize);
				}
			}
		}
		logger.debug(this + " `truncate` " + bitSize + " = " + result);
		assert result.getBitWidth() == bitSize;
		return result;
	}

	/**
	 * The shift to perform.
	 */
	private enum ShiftMode {
		SHL, SHR, SAR
	}

	/**
	 * Shift an interval using the given shift mode and an interval of shifts.
	 *
	 * @param t The interval of bit positions to shift by.
	 * @param m The shift mode.
	 * @return The shifted interval.
	 */
	private IntervalElement shiftSomeInterval(IntervalElement t, ShiftMode m) {
		logger.debug("Shifting " + this + " with " + t + " with mode " + m);
		assertCompatible(t);
		List<IntervalElement> results = new ArrayList<>();
		// find all possible shift amounts
		IntervalElement[] possibleShifts = t.intersection(interval(0L, (long)bitSize - 1L));
		for (IntervalElement ps : possibleShifts) {
			for (BitNumber s : ps) {
				// shift by each possible shift amount
				int k = (int) s.zExtLongValue();
				assert k >= 0 && k <= bitSize;
				if (m == ShiftMode.SHL) {
					IntervalElement tmp = truncate(bitSize - k).cast(bitSize);
					if (tmp.kind == IntervalKind.INTERVAL) {
						results.add(interval(tmp.minBits.shl(k), tmp.maxBits.shl(k)));
					} else if (!tmp.isBot()) {
						results.add(interval(0L, ~(bit(bitSize - 1) - 1L)));
					}
				} else if (m == ShiftMode.SHR) {
					if (southPole().isSubIntervalOf(this)) {
						results.add(interval(0L, bit(bitSize - k) - 1L));
					} else if (!isBot()) {
						assert !isTop();
						results.add(interval(minBits.shr(k), maxBits.shr(k)));
					}
				} else {
					assert m == ShiftMode.SAR;
					if (northPole().isSubIntervalOf(this)) {
						long tmp = bit(bitSize - k) - 1L;
						results.add(interval(~tmp, tmp));
					} else if (!isBot()) {
						assert !isTop();
						results.add(interval(minBits.sar(k), maxBits.sar(k)));
					}
				}
			}
		}
		// if other numbers were also possible, include zero in the result
		// (or -1 for some sar shifts)
		boolean includesZero = t.intersection(interval((long)bitSize, -1L)).length > 0;
		if (includesZero) {
			if (m == ShiftMode.SAR) {
				for (IntervalElement u : cut()) {
					assert u.kind == IntervalKind.INTERVAL;
					if (u.minBits.msb()) {
						results.add(number(-1L));
					} else {
						results.add(number(0L));
					}
				}
			} else {
				results.add(number(0L));
			}
		}
		// join all possible results
		return joins(bitSize, results);
	}

	@Override
	public IntervalElement shl(IntervalElement t) {
		assertCompatible(t);
		IntervalElement result = shiftSomeInterval(t, ShiftMode.SHL);
		logger.debug(this + " << " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement shr(IntervalElement t) {
		assertCompatible(t);
		IntervalElement result = shiftSomeInterval(t, ShiftMode.SHR);
		logger.debug(this + " >>> " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement sar(IntervalElement t) {
		assertCompatible(t);
		IntervalElement result = shiftSomeInterval(t, ShiftMode.SAR);
		logger.debug(this + " >> " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement eq(IntervalElement t) {
		final IntervalElement result;
		if (hasUniqueConcretization() && t.hasUniqueConcretization()) {
			result = getUniqueConcretization().equals(t.getUniqueConcretization()) ? TRUE_INTERVAL : FALSE_INTERVAL;
		} else {
			result = intersection(t).length > 0 ? TRUE_FALSE_INTERVAL : FALSE_INTERVAL;
		}
		logger.debug(this + " == " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement signedLessThan(IntervalElement t) {
		List<IntervalElement> acc = new ArrayList<>();
		for (IntervalElement u : splitNorth()) {
			for (IntervalElement v : t.splitNorth()) {
				acc.add(lt_w(true, u, v));
			}
		}
		IntervalElement result = joins(1, acc);
		logger.debug(this + " <_s " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement signedLessThanOrEqual(IntervalElement t) {
		List<IntervalElement> acc = new ArrayList<>();
		for (IntervalElement u : splitNorth()) {
			for (IntervalElement v : t.splitNorth()) {
				acc.add(leq_w(true, u, v));
			}
		}
		IntervalElement result = joins(1, acc);
		logger.debug(this + " <=_s " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement unsignedLessThan(IntervalElement t) {
		List<IntervalElement> acc = new ArrayList<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				acc.add(lt_w(false, u, v));
			}
		}
		IntervalElement result = joins(1, acc);
		logger.debug(this + " <_u " + t + " = " + result);
		return result;
	}

	@Override
	public IntervalElement unsignedLessThanOrEqual(IntervalElement t) {
		List<IntervalElement> acc = new ArrayList<>();
		for (IntervalElement u : splitSouth()) {
			for (IntervalElement v : t.splitSouth()) {
				acc.add(leq_w(false, u, v));
			}
		}
		IntervalElement result = joins(1, acc);
		logger.debug(this + " <=_u " + t + " = " + result);
		return result;
	}

	private static IntervalElement lt_w(boolean isSigned, IntervalElement s, IntervalElement t) {
		assert s.getBitWidth() == t.getBitWidth();
		assert s.isInterval();
		assert t.isInterval();
		IntervalElement[] x = s.intersection(t);
		if (x.length == 0) {
			// the intervals have no intersection
			// take two values and compare them
			// this works only of no interval crosses the north or south-pole, depending on the sign
			if (isSigned) {
				return number(BitNumber.valueOf(s.minBits.slt(t.minBits)));
			} else {
				return number(BitNumber.valueOf(s.minBits.ult(t.minBits)));
			}
		} else if (x.length == 1) {
			// we have at least one number in both, so false is always included
			if (s.hasUniqueConcretization()) {
				// s has just one value, so it can be at the upper limit of t
				if (t.hasUniqueConcretization()) {
					// t also has just one value, thus they are equal (intersection not empty)
					assert s.equals(t);
					return FALSE_INTERVAL;
				} else {
					// check whether s sits at the maximum of t
					return s.getUniqueConcretization().equals(t.maxBits) ? FALSE_INTERVAL : TRUE_FALSE_INTERVAL;
				}
			} else if (t.hasUniqueConcretization()) {
				// s has more than one number, but t has only one
				// check whether t sits at the minimum of s
				return t.getUniqueConcretization().equals(s.minBits) ? FALSE_INTERVAL : TRUE_FALSE_INTERVAL;
			}
		}
		// more than two numbers in both intervals, thus top
		return TRUE_FALSE_INTERVAL;
	}

	private static IntervalElement leq_w(boolean isSigned, IntervalElement s, IntervalElement t) {
		assert s.getBitWidth() == t.getBitWidth();
		assert s.isInterval();
		assert t.isInterval();
		IntervalElement[] x = s.intersection(t);
		if (x.length == 0) {
			// the intervals have no intersection
			// take two values and compare them
			// this works only of no interval crosses the north or south-pole, depending on the sign
			if (isSigned) {
				return number(BitNumber.valueOf(s.minBits.sleq(t.minBits)));
			} else {
				return number(BitNumber.valueOf(s.minBits.uleq(t.minBits)));
			}
		} else if (x.length == 1) {
			// we have at least one number in both, so true is always included
			if (s.hasUniqueConcretization()) {
				// s has just one value, so it can be at the lower limit of t
				if (t.hasUniqueConcretization()) {
					// t also has just one value, thus they are equal (intersection not empty)
					assert s.equals(t);
					return TRUE_INTERVAL;
				} else {
					// check whether s sits at the minimum of t
					return s.getUniqueConcretization().equals(t.minBits) ? TRUE_INTERVAL : TRUE_FALSE_INTERVAL;
				}
			} else if (t.hasUniqueConcretization()) {
				// s has more than one number, but t has only one
				// check whether t sits at the maximum of s
				return t.getUniqueConcretization().equals(s.maxBits) ? TRUE_INTERVAL : TRUE_FALSE_INTERVAL;
			}
		}
		// more than two numbers in both intervals, thus top
		return TRUE_FALSE_INTERVAL;
	}

	/**
	 * Compute the least upper bound of a set of intervals, ignoring anything outside of the range 0..modulus - 1 when
	 * considering which one is smaller.
	 *
	 * @param modulus The modulus.
	 * @param c The set of intervals.
	 * @return An interval containing all input intervals.
	 */
	static IntervalElement joinsMod(BitNumber modulus, Collection<IntervalElement> c) {
		assert !c.isEmpty();
		List<IntervalElement> s = new ArrayList<>(c.size());
		for (IntervalElement e : c) {
			s.add(e);
		}
		Collections.sort(s);
		logger.debug("** starting joinsMod " + modulus + " of " + s);
		int bitSize = s.iterator().next().bitSize;
		IntervalElement f = bot(bitSize);
		IntervalElement g = f;
		for (IntervalElement e : s) {
			if (e.isTop() || e.kind == IntervalKind.INTERVAL && e.maxBits.ult(e.minBits)) {
				f = f.joinMod(e, modulus);
			}
		}
		for (IntervalElement e : s) {
			g = biggerMod(g, f.gap(e), modulus);
			f = f.joinMod(e, modulus);
		}
		IntervalElement result = biggerMod(f.invert(), g, modulus).invert();
		logger.debug("Joins of " + s + " = " + result);
		for (IntervalElement e : s) {
			assert e.lessOrEqual(result) : "Element " + e + " should be in interval " + result + ", but wasn't.";
		}
		return result;

	}

	/**
	 * Return the bigger interval when considering only the range 0..modulus - 1.
	 *
	 * @param s The first interval.
	 * @param t The second interval.
	 * @param modulus The modulus.
	 * @return The bigger interval.
	 */
	private static IntervalElement biggerMod(IntervalElement s, IntervalElement t, BitNumber modulus) {
		return s.sizeMod(modulus).compareTo(t.sizeMod(modulus)) > 0 ? s : t;
	}

	/**
	 * Return the size of the part of this interval between 0 and modulus - 1.
	 *
	 * @param modulus The modulus.
	 * @return The size.
	 */
	BigInteger sizeMod(BitNumber modulus) {
		assert modulus != null;
		assert modulus.zExtLongValue() != 0L;
		BigInteger acc = BigInteger.ZERO;
		for (IntervalElement x : intersection(interval(modulus.valueOf(0L), modulus.dec()))) {
			acc = acc.add(x.size());
		}
		return acc;
	}

	/**
	 * Join two intervals, ignoring anything outside of 0..modulus - 1 when considering an interval as smaller than another.
	 *
	 * @param t The other interval.
	 * @param modulus The modulus.
	 * @return The smallest interval containing both when intersected with 0..modulus - 1
	 */
	private IntervalElement joinMod(IntervalElement t, BitNumber modulus) {
		IntervalElement x = join(t);
		IntervalElement y = x.invert().join(this).join(t);
		return x.sizeMod(modulus).compareTo(y.sizeMod(modulus)) < 1 ? x : y;
	}

	@Override
	public IntervalElement widen(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement result;
		if (isBot()) {
			result = t;
		} else if (t.isBot() || isTop()) {
			result = this;
		} else if (t.isTop()) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (size().compareTo(BigInteger.valueOf(2L).pow(bitSize - 1)) >= 0) {
			result = top();
		} else {
			IntervalElement tmp = join(t);
			BitNumber two = BitNumber.valueOf(2L, bitSize);
			if (tmp.equals(interval(minBits, t.maxBits))) {
				result = interval(minBits, t.maxBits).join(
						interval(minBits, maxBits.mul(two).sub(minBits).inc()));
			} else if (tmp.equals(interval(t.minBits, maxBits))) {
				result = interval(t.minBits, maxBits).join(
						interval(minBits.mul(two).sub(maxBits).dec(), maxBits));
			} else if (t.hasElement(minBits) && t.hasElement(maxBits)) {
				result = t.join(interval(t.minBits, t.minBits.add(maxBits.mul(two)).sub(minBits.mul(two)).inc())).join(this);
			} else {
				result = top();
			}
		}
		logger.debug(this + " `widen` " + t + " = " + result);
		assert lessOrEqual(result) && t.lessOrEqual(result) : "Widen returned something smaller than one of the arguments";
		assert equals(result) || result.isTop() || result.size().compareTo(size().add(size())) >= 0 : "Widen did not fulfill property of the paper";
		return result;
	}

	@Override
	public Iterator<BitNumber> iterator() {
		if (isBot()) {
			return new BotIntervalIterator();
		} else if (isTop()) {
			return specificInterval(BitNumber.uMinVal(bitSize), BitNumber.uMaxVal(bitSize)).iterator();
		} else {
			return new Iterator<BitNumber>() {
				private BitNumber pos = minBits;
				private boolean done = false;

				@Override
				public boolean hasNext() {
					return !done;
				}

				@Override
				public BitNumber next() {
					if (hasNext()) {
						BitNumber val = pos;
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

	@Override
	public Pair<IntervalElement, IntervalElement> assumeULeq(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement newS;
		if (t.isBot()) {
			newS = bot(bitSize);
		} else if (t.hasElement(bit(bitSize) - 1L)) {
			newS = this;
		} else {
			assert t.kind == IntervalKind.INTERVAL;
			newS = meet(interval(BitNumber.valueOf(0L, bitSize), t.maxBits));
		}
		final IntervalElement newT;
		if (isBot()) {
			newT = bot(bitSize);
		} else if (hasElement(0L)) {
			newT = t;
		} else {
			assert kind == IntervalKind.INTERVAL;
			newT = t.meet(interval(minBits, BitNumber.valueOf(bit(bitSize) - 1L, bitSize)));
		}
		Pair<IntervalElement, IntervalElement> result = new Pair<>(newS, newT);
		logger.debug("assume " + this + " <= " + t + ": " + result);
		return result;
	}

	@Override
	public Pair<IntervalElement, IntervalElement> assumeSLeq(IntervalElement t) {
		assertCompatible(t);
		final IntervalElement newS;
		if (t.isBot()) {
			newS = bot(bitSize);
		} else if (t.hasElement(bit(bitSize - 1) - 1L)) {
			newS = this;
		} else {
			assert t.kind == IntervalKind.INTERVAL;
			newS = meet(interval(BitNumber.valueOf(bit(bitSize) - 1L, bitSize), t.maxBits));
		}
		final IntervalElement newT;
		if (isBot()) {
			newT = bot(bitSize);
		} else if (hasElement(bit(bitSize) - 1L)) {
			newT = t;
		} else {
			assert kind == IntervalKind.INTERVAL;
			newT = t.meet(interval(minBits, BitNumber.valueOf(bit(bitSize - 1) - 1L, bitSize)));
		}
		Pair<IntervalElement, IntervalElement> result = new Pair<>(newS, newT);
		logger.debug("assume " + this + " <= " + t + ": " + result);
		return result;
	}

	/**
	 * Different kinds of intervals.
	 */
	private enum IntervalKind {
		TOP, INTERVAL, BOT
	}

	private static class BotIntervalIterator implements Iterator<BitNumber> {
		@Override
		public boolean hasNext() {
			return false;
		}

		@Override
		public BitNumber next() {
			throw new NoSuchElementException("Called next on BOT interval");
		}

		@Override
		public void remove() {
			assert false : "Called remove on BOT interval";
		}
	}
}
