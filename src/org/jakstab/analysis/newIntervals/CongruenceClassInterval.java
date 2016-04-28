package org.jakstab.analysis.newIntervals;

import org.jakstab.Options;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.newIntervals.abstracted.AbstractDomain;
import org.jakstab.analysis.newIntervals.abstracted.AbstractEvaluator;
import org.jakstab.analysis.newIntervals.abstracted.Boxable;
import org.jakstab.analysis.newIntervals.statistic.Statistic;
import org.jakstab.analysis.newIntervals.utils.BitNumber;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.ExpressionFactory;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.*;

import java.lang.ref.WeakReference;
import java.math.BigInteger;
import java.util.*;

import static org.jakstab.analysis.newIntervals.CongruenceClassInterval.RevMode.*;
import static org.jakstab.analysis.newIntervals.IntervalElement.interval;
import static org.jakstab.rtl.expressions.RTLBitRange.bitMask;

final class CongruenceClassInterval implements AbstractDomain<CongruenceClassInterval>, Boxable<CongruenceClassInterval> {

	/**
	 * Logger.
	 */
	private static final Logger logger = Logger.getLogger(CongruenceClassInterval.class);

	/**
	 * Range valid numbers are in.
	 */
	private final IntervalElement range;

	/**
	 * Range the remainder has to be in.
	 */
	private final IntervalElement modRange;

	/**
	 * Modulus.
	 */
	private final BitNumber modulus;

	/**
	 * Number of bits for this cc-interval. Often denoted w in comments.
	 */
	private final int bitSize;

	/**
	 * Kind of the interval (top, bot, zero, mod).
	 */
	private final CCIntervalKind kind;

	/**
	 * Cache for intervals, see {@link BitNumber}.
	 */
	private static final List<Map<CongruenceClassInterval, WeakReference<CongruenceClassInterval>>> cache = new ArrayList<>(64);

	/**
	 * Cached true value.
	 */
	static final CongruenceClassInterval TRUE_CC_INTERVAL = new CongruenceClassInterval(IntervalElement.TRUE_INTERVAL);

	/**
	 * Cached false value.
	 */
	static final CongruenceClassInterval FALSE_CC_INTERVAL = new CongruenceClassInterval(IntervalElement.FALSE_INTERVAL);

	/**
	 * Cached TOP for 1-bit intervals (true and false).
	 */
	private static final CongruenceClassInterval TRUE_FALSE_CC_INTERVAL = new CongruenceClassInterval(1, CCIntervalKind.TOP);

	static {
		// initialize the cache.
		for (int i = 0; i < 64; i++) {
			cache.add(new HashMap<CongruenceClassInterval, WeakReference<CongruenceClassInterval>>());
		}
		cache.get(0).put(TRUE_CC_INTERVAL, new WeakReference<>(TRUE_CC_INTERVAL));
		cache.get(0).put(FALSE_CC_INTERVAL, new WeakReference<>(FALSE_CC_INTERVAL));
		cache.get(0).put(TRUE_FALSE_CC_INTERVAL, new WeakReference<>(TRUE_FALSE_CC_INTERVAL));
	}

	/**
	 * Lookup an element in the cache and if it exists, use the reference from the cache.
	 *
	 * @param tmp The element to look up.
	 * @return Something equal to tmp.
	 */
	private static CongruenceClassInterval getFromCache(CongruenceClassInterval tmp) {
		Statistic.countCCIntervalElementUse();
		Map<CongruenceClassInterval, WeakReference<CongruenceClassInterval>> thisCache = cache.get(tmp.bitSize - 1);
		WeakReference<CongruenceClassInterval> found = thisCache.get(tmp);
		if (found == null) {
			thisCache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		CongruenceClassInterval result = found.get();
		if (result == null) {
			Statistic.countBitNumberUse();
			thisCache.put(tmp, new WeakReference<>(tmp));
			return tmp;
		}
		Statistic.countCCIntervalElementReuse();
		return result;
	}

	/**
	 * Create a new top or bot cc-interval.
	 *
	 * @param bitSize Number of bits in the cc-interval.
	 * @param kind Kind of the interval, may not be zero or mod.
	 */
	private CongruenceClassInterval(int bitSize, CCIntervalKind kind) {
		assert kind == CCIntervalKind.TOP || kind == CCIntervalKind.BOT;
		assert bitSize >= 0 && bitSize <= 64;

		range = null;
		modRange = null;
		modulus = null;
		this.bitSize = bitSize;
		this.kind = kind;
		Statistic.countCCIntervalElementCreate();
		logger.debug("Created new cc-interval " + this);
	}

	private CongruenceClassInterval(IntervalElement range) {
		assert range != null;
		assert range.getBitWidth() >= 0 && range.getBitWidth() <= 64;

		if (range.isBot()) {
			this.range = null;
			kind = CCIntervalKind.BOT;
		} else if (range.isTop()) {
			this.range = null;
			kind = CCIntervalKind.TOP;
		} else {
			this.range = range;
			kind = CCIntervalKind.ZERO;
		}
		modRange = null;
		modulus = null;
		bitSize = range.getBitWidth();
		Statistic.countCCIntervalElementCreate();
		logger.debug("Created new cc-interval " + this);
	}

	private static IntervalElement constrainModRange(IntervalElement modRange, BitNumber modulus) {
		assert modRange.getBitWidth() == modulus.getBitWidth();
		final IntervalElement result;
		if (modRange.isTop()) {
			result = interval(modulus.valueOf(0L), modulus.dec());
		} else if (modRange.isBot()) {
			result = modRange; // bot
		} else if (modRange.maxBits.ult(modRange.minBits)) {
			if (modRange.minBits.ult(modulus)) {
				result = modRange;
			} else {
				result = interval(modulus.valueOf(0L), modRange.maxBits.uMin(modulus.dec()));
			}
		} else if (modRange.minBits.ugeq(modulus)) {
			result = modRange.bot();
		} else if (modRange.maxBits.ugeq(modulus)) {
			result = interval(modRange.minBits, modulus.dec());
		} else {
			result = modRange;
		}
		assert result.lessOrEqual(modRange);
		logger.debug("constrainModRange " + modRange + ' ' + modulus + " = " + result);
		return result;
	}

	@Override
	public Iterator<BitNumber> iterator() {
		if (isTop()) {
			return IntervalElement.top(bitSize).iterator();
		} else if (isBot()) {
			return IntervalElement.bot(bitSize).iterator();
		} else if (kind == CCIntervalKind.ZERO) {
			return range.iterator();
		} else {
			assert kind == CCIntervalKind.MOD;
			return new Iterator<BitNumber>() {
				final Iterator<BitNumber> inner = range.iterator();
				BitNumber cachedNext = null;

				@Override
				public boolean hasNext() {
					cacheNext();
					return cachedNext != null;
				}

				@Override
				public BitNumber next() {
					cacheNext();
					if (cachedNext != null) {
						BitNumber r = cachedNext;
						cachedNext = null;
						return r;
					}
					throw new NoSuchElementException("called next on empty iterator");
				}

				@Override
				public void remove() {
					throw new UnsupportedOperationException("remove not implemented");
				}

				private void cacheNext() {
					if (cachedNext == null) {
						while (inner.hasNext()) {
							BitNumber candidate = inner.next();
							if (modRange.hasElement(candidate.urem(modulus))) {
								cachedNext = candidate;
								return;
							}
						}
					}
				}
			};
		}
	}

	private CongruenceClassInterval number(long n) {
		return number(BitNumber.valueOf(n, bitSize));
	}

	public static CongruenceClassInterval number(BitNumber n) {
		return getFromCache(new CongruenceClassInterval(IntervalElement.number(n)));
	}

	private static CongruenceClassInterval zeroInterval(IntervalElement range) {
		return getFromCache(new CongruenceClassInterval(range));
	}

	private static CongruenceClassInterval modInterval(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		return getFromCache(new CongruenceClassInterval(range, modRange, modulus));
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		return new GenericValuationState<>(CongruenceClassIntervalFactory.getFactory()).projectionFromConcretization(expressions);
	}

	public static Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression[] expressions, AbstractEvaluator<CongruenceClassInterval> s) {
		logger.debug("projection from concretization for " + expressions.length + " expressions: " + Arrays.toString(expressions));
		Tuple<Set<RTLNumber>> cValues = new Tuple<>(expressions.length);
		for (int i = 0; i < expressions.length; i++) {
			CongruenceClassInterval aValue = s.evalExpression(expressions[i]).abstractGet();
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
					// TODO: limit size?
					tmp.add(ExpressionFactory.createNumber(l.sExtLongValue(), aValue.bitSize));
				}
				cValues.set(i, tmp);
			}
		}
		Set<Tuple<RTLNumber>> result = Sets.crossProduct(cValues);
		logger.debug("Projected " + result);
		return result;
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
		for (BitNumber l : this) {
			s.add(ExpressionFactory.createNumber(l.sExtLongValue(), bitSize));
		}
		return s;
	}

	@Override
	public CongruenceClassInterval abstractGet() {
		return this;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return kind == CCIntervalKind.ZERO && range.hasUniqueConcretization();
	}

	@Override
	public BitNumber getUniqueConcretization() {
		assert hasUniqueConcretization();
		return range.getUniqueConcretization();
	}

	private static CongruenceClassInterval maybeDropCC(IntervalElement s1, IntervalElement s2, CongruenceClassInterval x) {
		if (x.isTop()) {
			return zeroInterval(s1.join(s2));
		} else if (x.isBot()) {
			return x;
		} else if (x.kind == CCIntervalKind.ZERO) {
			CongruenceClassInterval s = zeroInterval(s1).join(zeroInterval(s2));
			if (s.isTop()) {
				return x;
			} else if (s.isBot()) {
				return s;
			} else if (s.kind == CCIntervalKind.ZERO) {
				IntervalElement[] tmp = x.range.intersection(s.range);
				return zeroInterval(IntervalElement.joins(x.bitSize, Arrays.asList(tmp)));
			} else {
				assert s.kind == CCIntervalKind.MOD;
				IntervalElement[] tmp = x.range.intersection(s.range);
				return modInterval(IntervalElement.joins(x.bitSize, Arrays.asList(tmp)), s.modRange, s.modulus);
			}
		} else {
			return x;
		}
	}

	@Override
	public CongruenceClassInterval join(LatticeElement l) {
		CongruenceClassInterval t = (CongruenceClassInterval) l;
		final CongruenceClassInterval result;
		if (isTop() || t.isBot() || t.lessOrEqual(this)) {
			result = this;
		} else if (t.isTop() || isBot() || lessOrEqual(t)) {
			result = t;
		} else if (hasUniqueConcretization()) {
			if (t.hasUniqueConcretization()) {
				BitNumber a = getUniqueConcretization();
				BitNumber b = t.getUniqueConcretization();
				if (a.equals(b)) {
					result = this;
				} else {
					BitNumber x = a.uMin(b);
					BitNumber y = a.uMax(b);
					BitNumber c = y.sub(x);
					BitNumber n = a.urem(c);
					assert b.urem(c).equals(n);
					result = modInterval(IntervalElement.number(x).join(IntervalElement.number(y)), IntervalElement.number(n), c);
				}
			} else {
				result = t.join(this);
			}
		} else if (t.hasUniqueConcretization() && kind == CCIntervalKind.MOD) {
			BitNumber a = t.getUniqueConcretization();
			BitNumber n = a.urem(modulus);
			if (modRange.hasElement(n)) {
				result = modInterval(range.join(IntervalElement.number(a)), modRange, modulus);
			} else {
				result = modInterval(range.join(IntervalElement.number(n)), modRange.join(IntervalElement.number(n)), modulus);
			}
		} else if (kind == CCIntervalKind.ZERO && t.kind == CCIntervalKind.ZERO) {
			BitNumber n = BitNumber.uMaxVal(bitSize);
			IntervalElement c = range.join(t.range);
			BitNumber z = BitNumber.valueOf(0L, bitSize);
			// if 0 is included, include also the max-bound
			if (!(range.hasElement(n) || t.range.hasElement(n)) || range.hasElement(z) || t.range.hasElement(z)) {
				// c covers the smaller gap between a and b, while the congruence class
				// covers the larger gap and excludes the smaller gap
				IntervalElement[] x = { range, t.range, c.invert() };
				result = modInterval(c, IntervalElement.joins(bitSize, Arrays.asList(x)), n);
			} else {
				// just plain interval
				result = zeroInterval(c);
			}
		} else if (kind == CCIntervalKind.MOD && t.kind == CCIntervalKind.ZERO) {
			List<IntervalElement> x = t.range.num_rem_w(modulus);
			x.add(modRange);
			result = maybeDropCC(range, t.range, modInterval(range.join(t.range), IntervalElement.joins(bitSize, x), modulus));
		} else if (kind == CCIntervalKind.ZERO && t.kind == CCIntervalKind.MOD) {
			List<IntervalElement> x = range.num_rem_w(t.modulus);
			x.add(t.modRange);
			result = maybeDropCC(range, t.range, modInterval(range.join(t.range), IntervalElement.joins(bitSize, x), t.modulus));
		} else {
			assert kind == CCIntervalKind.MOD;
			assert t.kind == CCIntervalKind.MOD;
			BitNumber m = modulus.gcd(t.modulus);
			List<IntervalElement> x = range.num_rem_w(m);
			x.addAll(t.range.num_rem_w(m));
			result = maybeDropCC(range, t.range, modInterval(range.join(t.range), IntervalElement.joins(bitSize, x), m));
		}
		assert lessOrEqual(result);
		assert t.lessOrEqual(result);
		logger.debug(this + " `join` " + t + " = " + result);
		return result;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		CongruenceClassInterval t = (CongruenceClassInterval) l;
		final boolean result;
		if (isTop()) {
			result = t.isTop();
		} else if (isBot()) {
			result = true;
		} else if (kind == CCIntervalKind.ZERO) {
			if (t.isTop()) {
				result = true;
			} else if (t.isBot()) {
				result = false;
			} else if (t.kind == CCIntervalKind.ZERO) {
				result = range.lessOrEqual(t.range);
			} else {
				assert t.kind == CCIntervalKind.MOD;
				if (range.lessOrEqual(t.range)) {
					boolean tmp = true;
					for (IntervalElement x : range.num_rem_w(t.modulus)) {
						tmp = tmp && x.lessOrEqual(t.modRange);
					}
					result = tmp;
				} else {
					result = false;
				}
			}
		} else {
			assert kind == CCIntervalKind.MOD;
			if (t.isTop()) {
				result = true;
			} else if (t.isBot()) {
				result = false;
			} else if (t.kind == CCIntervalKind.ZERO) {
				if (range.lessOrEqual(t.range)) {
					// range is an over-approximation of s, so we are done
					result = true;
				} else {
					// range includes some numbers not in this, so maybe they are the problem
					boolean tmp = true;
					for (IntervalElement missing : range.intersection(t.range.invert())) {
						for (IntervalElement x : missing.num_rem_w(modulus)) {
							tmp = tmp && x.intersection(modRange).length == 0;
						}
					}
					result = tmp;
				}
			} else {
				assert t.kind == CCIntervalKind.MOD;
				BitNumber z = modulus.valueOf(0L);
				if (range.lessOrEqual(t.range) && modulus.urem(t.modulus).equals(z)) {
					boolean tmp = true;
					for (IntervalElement r : modRange.intersection(interval(z, modulus.dec()))) {
						for (IntervalElement x : r.num_rem_w(t.modulus)) {
							tmp = tmp && x.lessOrEqual(t.modRange);
						}
					}
					result = tmp;
				} else {
					// actually, here one interval still could be a sub-interval of the other. This happens if they would
					// normally be incomparable in an infinite number ring, but because the ring is actually finite, the
					// cases where one number is in one but not the other interval never happen...
					result = false;
				}
			}
		}
		logger.debug(this + " `lessOrEqual` " + t + " = " + result);
		return result;
	}

	@Override
	public boolean isTop() {
		return kind == CCIntervalKind.TOP;
	}

	@Override
	public boolean isBot() {
		return kind == CCIntervalKind.BOT;
	}

	@Override
	public boolean hasElement(RTLNumber e) {
		return hasElement(BitNumber.valueOf(e));
	}

	@Override
	public boolean hasElement(BitNumber e) {
		assert e.getBitWidth() == bitSize;
		return isTop() || !isBot() && range.hasElement(e) && (kind != CCIntervalKind.MOD || modRange.hasElement(e.urem(modulus)));
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> joins(Collection<CongruenceClassInterval> c) {
		return joinsCC(bitSize, c);
	}

	/**
	 * True if addition of s and t never overflows.
	 *
	 * @param s First interval.
	 * @param t Second interval.
	 * @return True if s + t never overflows.
	 */
	private static boolean additionNoOverflow(IntervalElement s, IntervalElement t) {
		if (s.isBot() || t.isBot()) {
			return true;
		} else {
			BigInteger a = s.intervalMax().unsignedBigValue().add(t.intervalMax().unsignedBigValue());
			BigInteger b = s.maxIntervalSize();
			return a.compareTo(b) < 0;
		}
	}

	/**
	 * Create the congruence information for addition. Extends the interval t by t + (m - 2^w `rem` m), covering the case of overflow.
	 *
	 * @param t The modulus interval.
	 * @param m The modulus.
	 * @return The result.
	 */
	private static IntervalElement mkAddCongruence(IntervalElement t, BitNumber m) {
		IntervalElement x = t.num_rem_cc(m);
		List<IntervalElement> c = new ArrayList<>();
		c.add(x);
		BitNumber overflowPart = m.valueOf(t.maxIntervalSize().remainder(m.unsignedBigValue()).longValue());
		c.add(x.add(IntervalElement.number(m.sub(overflowPart))).num_rem_cc(m));
		c.add(x.add(IntervalElement.number(overflowPart)).num_rem_cc(m));
		return IntervalElement.joins(m.getBitWidth(), c);
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> add(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			if (t.kind == CCIntervalKind.MOD) {
				BitNumber m = modulus.gcd(t.modulus);
				if (additionNoOverflow(range, t.range)) {
					result = modInterval(range.add(t.range), modRange.add(t.modRange).num_rem_cc(m), m);
				} else {
					result = modInterval(range.add(t.range), mkAddCongruence(modRange.add(t.modRange), m), m);
				}
			} else {
				if (additionNoOverflow(range, t.getRange())) {
					result = modInterval(range.add(t.getRange()), modRange.add(t.getRange()).num_rem_cc(modulus), modulus);
				} else {
					result = modInterval(range.add(t.getRange()), mkAddCongruence(modRange.add(t.getRange()), modulus), modulus);
				}
			}
		} else if (t.kind == CCIntervalKind.MOD) {
			if (additionNoOverflow(getRange(), t.range)) {
				result = modInterval(getRange().add(t.range), getRange().add(t.modRange).num_rem_cc(t.modulus), t.modulus);
			} else {
				result = modInterval(getRange().add(t.range), mkAddCongruence(getRange().add(t.modRange), t.modulus), t.modulus);
			}
		} else {
			result = zeroInterval(getRange().add(t.getRange()));
		}
		logger.debug(this + " + " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> sub(CongruenceClassInterval t) {
		CongruenceClassInterval result = add(t.negate().abstractGet()).abstractGet();
		logger.debug(this + " - " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> negate() {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			List<IntervalElement> xs = modRange.negate().num_rem_w(modulus);
			if (modRange.hasElement(modulus.valueOf(0L))) {
				BigInteger tmp = modRange.maxIntervalSize().remainder(modulus.unsignedBigValue());
				xs.add(IntervalElement.number(modulus.valueOf(tmp.longValue())));
			}
			result = modInterval(range.negate(), IntervalElement.joins(bitSize, xs), modulus);
		} else {
			result = zeroInterval(getRange().negate());
		}
		logger.debug('-' + toString() + " = " + result);
		return result;
	}

	/**
	 * Double the bitsize of an interval (for multiplication).
	 *
	 * @return An interval with twice the bitsize.
	 */
	private CongruenceClassInterval extentBitSize() {
		switch (bitSize) {
			case 1:
				assert !Options.failFast.getValue() : "Extending 1-bit cc-interval";
				logger.warn("Extending 1-bit cc-interval!");
			case 8:
			case 16:
			case 32:
				return cast(bitSize * 2).abstractGet();
			case 64:
				return this;
			default:
				assert !Options.failFast.getValue() : "Extending " + bitSize + "-bit cc-interval";
				logger.warn("Extending " + bitSize + "-bit cc-interval!");
				return cast(Math.min(64, bitSize * 2)).abstractGet();
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> mul(CongruenceClassInterval t) {
		// TODO if both intervals are below 64 bits, we can actually do more here as overflow can not happen
		return extentBitSize().mulHelper(t.extentBitSize());
	}

	private CongruenceClassInterval mulHelper(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (hasUniqueConcretization()) {
			if (t.hasUniqueConcretization()) {
				result = number(getUniqueConcretization().mul(t.getUniqueConcretization()));
			} else {
				BitNumber u = getUniqueConcretization();
				if (u.zExtLongValue() == 0L) {
					// deal with bot in the interval domain
					result = zeroInterval(t.getRange().mul(IntervalElement.number(u)));
				} else if (u.zExtLongValue() == 1L) {
					result = t;
				} else {
					BigInteger n = range.maxIntervalSize();
					BigInteger uu = u.unsignedBigValue();
					BitNumber us = BitNumber.valueOf(uu.gcd(n).longValue(), bitSize);
					BitNumber z = BitNumber.valueOf(0L, bitSize);
					IntervalElement ui = IntervalElement.number(u);
					if (t.isTop()) {
						result = modInterval(IntervalElement.top(bitSize), IntervalElement.number(z), us);
					} else if (t.isBot()) {
						result = t; // bot
					} else if (t.kind == CCIntervalKind.ZERO) {
						if (n.compareTo(t.range.intervalMax().unsignedBigValue().multiply(uu)) > 0) {
							// no overflow can occur
							result = modInterval(ui.mul(t.range), IntervalElement.number(z), u);
						} else {
							// overflow occurs
							result = modInterval(ui.mul(t.range), IntervalElement.number(z), us);
						}
					} else {
						assert t.kind == CCIntervalKind.MOD;
						if (n.compareTo(t.range.intervalMax().unsignedBigValue().multiply(uu)) > 0) {
							BitNumber r = t.modulus.mul(u);
							IntervalElement tmp = IntervalElement.joins(bitSize, Arrays.asList(ui.mul(t.range).intersection(ui.mul(t.modRange))));
							if (t.modulus.uMulOverflow(u)) {
								if (r.zExtLongValue() == 0L) {
									// overflow in modulus, but exactly to a multiple of 2^w
									result = modInterval(tmp, IntervalElement.number(z), u);
								} else {
									// overflow in modulus
									result = zeroInterval(tmp);
								}
							} else {
								// no overflow as (max (t ∩ [0..m-1])) < intervalMax s holds
								result = modInterval(ui.mul(t.range), ui.mul(t.modRange), r);
							}
						} else {
							BigInteger m = uu.multiply(t.modulus.unsignedBigValue()).gcd(n);
							if (m.equals(n)) {
								result = zeroInterval(IntervalElement.joins(bitSize, Arrays.asList(ui.mul(t.range).intersection(ui.mul(t.modRange)))));
							} else {
								// overflow occurs
								BitNumber m2 = BitNumber.valueOf(m.longValue(), bitSize);
								result = modInterval(ui.mul(t.range), ui.mul(t.modRange).num_rem_cc(m2), m2);
							}
						}
					}
				}
			}
		} else {
			if (t.hasUniqueConcretization()) {
				// avoid duplication
				result = t.mulHelper(this);
			} else {
				result = zeroInterval(getRange().mul(t.getRange()));
			}
		}
		logger.debug(this + " * " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> unsignedDiv(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().unsignedDiv(t.getRange()));
		logger.debug(this + " /u " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> signedDiv(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().signedDiv(t.getRange()));
		logger.debug(this + " /s " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> unsignedRem(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (t.hasUniqueConcretization()) {
			BitNumber u = t.getUniqueConcretization();
			if (u.zExtLongValue() == 0L) {
				result = bot();
			} else if (kind == CCIntervalKind.MOD) {
				if (modulus.urem(u).zExtLongValue() == 0L) {
					IntervalElement tmp = IntervalElement.number(u);
					result = zeroInterval(IntervalElement.joins(bitSize, Arrays.asList(range.unsignedRem(tmp).intersection(modRange.unsignedRem(tmp)))));
				} else {
					result = modInterval(range.unsignedRem(IntervalElement.number(u)), IntervalElement.joinsMod(u, range.num_rem_w(u)), u);
				}
			} else {
				result = modInterval(getRange().unsignedRem(IntervalElement.number(u)), IntervalElement.joinsMod(u, getRange().num_rem_w(u)), u);
			}
		} else {
			result = zeroInterval(getRange().unsignedRem(t.getRange()));
		}
		logger.debug(this + " %u " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> signedRem(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().signedRem(t.getRange()));
		logger.debug(this + " %s " + t + " = " + result);
		return result;
	}

	/**
	 *  Given some congruence range, the current modulus and a new modulus, extend the range to the new modulus.
	 *
	 *  THIS ONLY WORKS WITH POWER-OF-TWO congruences!
	 *
	 * @param s The range.
	 * @param curSize The current range.
	 * @param newSize The new range.
	 * @return The result.
	 */
	private static IntervalElement extendBitRange(IntervalElement s, BitNumber curSize, BitNumber newSize) {
		assert curSize.log2n().hasValue();
		assert newSize.log2n().hasValue();
		assert curSize.uleq(newSize);
		BitNumber m = newSize.dec();
		final IntervalElement result;
		if (curSize.equals(newSize)) {
			result = s;
		} else {
			assert !s.isBot();
			IntervalElement[] xs = s.splitSouth();
			assert xs.length > 0 && xs.length <= 2;
			if (xs.length == 1) {
				IntervalElement x = xs[0];
				if (curSize.dec().equals(x.maxBits)) {
					result = interval(x.minBits, m);
				} else {
					// interval from a..b, so extend to a..m or cur..b, depending on which is better
					IntervalElement a = interval(x.minBits, m);
					IntervalElement b = interval(curSize, x.maxBits);
					if (a.sizeMod(newSize).compareTo(b.sizeMod(newSize)) < 0) {
						result = a;
					} else {
						result = b;
					}
				}
			} else {
				// interval from 0..b + c..max, so extend to 0..b + min c m..max
				result = interval(xs[1].minBits.uMin(m), xs[0].maxBits);
			}
		}
		assert IntervalElement.bigger(s, result).equals(result) : "extendBitRange made result smaller";
		assert result.hasElement(m);
		return result;
	}

	private static CongruenceClassInterval or_w1(IntervalElement s, IntervalElement t) {
		// no information, so not much to do here
		return zeroInterval(s.or(t));
	}

	private static CongruenceClassInterval or_w2(IntervalElement range, IntervalElement modRange, BitNumber modulus, IntervalElement range2) {
		if (modulus.log2n().hasValue()) {
			// okay, we have a power of two. assume 0..2^n-1 for the other congruence information
			return modInterval(range.or(range2), modRange.or(interval(BitNumber.valueOf(0L, range.getBitWidth()), modulus.dec())), modulus);
		} else {
			// drop useless information
			return or_w1(range, range2);
		}
	}

	private static CongruenceClassInterval or_w3(IntervalElement range1, IntervalElement modRange1, BitNumber modulus1, IntervalElement range2, IntervalElement modRange2, BitNumber modulus2) {
		if (modulus1.log2n().hasValue()) {
			if (modulus1.equals(modulus2)) {
				// same congruence and a power of two. so we compute the bitwise or everywhere and are done
				return modInterval(range1.or(range2), modRange1.or(modRange2), modulus1);
			} else if (modulus2.log2n().hasValue()) {
				// different congruences, but powers of two. extend the ranges.
				BitNumber m = modulus1.uMax(modulus2);
				return modInterval(range1.or(range2), extendBitRange(modRange1, modulus1, m).or(extendBitRange(modRange2, modulus2, m)), m);
			} else {
				// just one power of two. or_w2 handles this
				return or_w2(range1, modRange1, modulus1, range2);
			}
		} else if (modulus2.log2n().hasValue()) {
			// same as above
			return or_w2(range2, modRange2, modulus2, range1);
		} else {
			// drop useless information
			return or_w1(range1, range2);
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> or(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			if (t.kind == CCIntervalKind.MOD) {
				result = or_w3(range, modRange, modulus, t.range, t.modRange, t.modulus);
			} else {
				result = or_w2(range, modRange, modulus, t.getRange());
			}
		} else if (t.kind == CCIntervalKind.MOD) {
			result = or_w2(t.range, t.modRange, t.modulus, getRange());
		} else {
			result = or_w1(getRange(), t.getRange());
		}
		logger.debug(this + " | " + t + " = " + result);
		return result;
	}

	private static CongruenceClassInterval and_w1(IntervalElement s, IntervalElement t) {
		// no information, so not much to do here
		return zeroInterval(s.and(t));
	}

	private static CongruenceClassInterval and_w2(IntervalElement range, IntervalElement modRange, BitNumber modulus, IntervalElement range2) {
		if (modulus.log2n().hasValue()) {
			// okay, we have a power of two. assume 0..2^n-1 for the other congruence information
			return modInterval(range.and(range2), modRange.and(interval(BitNumber.valueOf(0L, range.getBitWidth()), modulus.dec())), modulus);
		} else {
			// drop useless information
			return and_w1(range, range2);
		}
	}

	private static CongruenceClassInterval and_w3(IntervalElement range1, IntervalElement modRange1, BitNumber modulus1, IntervalElement range2, IntervalElement modRange2, BitNumber modulus2) {
		if (modulus1.log2n().hasValue()) {
			if (modulus1.equals(modulus2)) {
				// same congruence and a power of two. so we compute the bitwise and everywhere and are done
				return modInterval(range1.and(range2), modRange1.and(modRange2), modulus1);
			} else if (modulus2.log2n().hasValue()) {
				// different congruences, but powers of two. extend the ranges.
				BitNumber m = modulus1.uMax(modulus2);
				return modInterval(range1.and(range2), extendBitRange(modRange1, modulus1, m).and(extendBitRange(modRange2, modulus2, m)), m);
			} else {
				// just one power of two. and_w2 handles this
				return and_w2(range1, modRange1, modulus1, range2);
			}
		} else if (modulus2.log2n().hasValue()) {
			// same as above
			return and_w2(range2, modRange2, modulus2, range1);
		} else {
			// drop useless information
			return and_w1(range1, range2);
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> and(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (hasUniqueConcretization()) {
			BitNumber n = getUniqueConcretization();
			if (n.zExtLongValue() == 0L) {
				result = zeroInterval(t.getRange().and(IntervalElement.number(n)));
			} else if (n.equals(n.uMaxVal())) {
				// all bits set, no-op (also avoids division by 0 in x `rem` (n + 1))
				result = t;
			} else if (t.hasUniqueConcretization()) {
				result = number(n.and(t.getUniqueConcretization()));
			} else if (t.isTop()) {
				result = zeroInterval(IntervalElement.number(n).and(IntervalElement.top(bitSize)));
			} else if (t.isBot()) {
				result = t; // bot
			} else if (t.kind == CCIntervalKind.ZERO) {
				result = zeroInterval(IntervalElement.number(n).and(t.range));
			} else {
				assert t.kind == CCIntervalKind.MOD;
				if (n.inc().log2n().hasValue()) {
					// n has all lower bits set, so n+1 is a single bit/power of 2
					if (t.modulus.urem(n.inc()).equals(n.valueOf(0L))) {
						// m is divisible by n + 1
						result = zeroInterval(IntervalElement.number(n).and(t.modRange));
					} else {
						// n has a single bit set, so it will either be 0 or n
						result = modInterval(t.range.and(IntervalElement.number(n)), IntervalElement.number(n.valueOf(0L)), n);
					}
				} else {
					result = zeroInterval(IntervalElement.number(n).and(t.range));
				}
			}
		} else {
			if (t.hasUniqueConcretization()) {
				// avoid duplication
				return t.and(this);
			} else {
				if (kind == CCIntervalKind.MOD) {
					if (t.kind == CCIntervalKind.MOD) {
						result = and_w3(range, modRange, modulus, t.range, t.modRange, t.modulus);
					} else {
						result = and_w2(range, modRange, modulus, t.getRange());
					}
				} else if (t.kind == CCIntervalKind.MOD) {
					result = and_w2(t.range, t.modRange, t.modulus, getRange());
				} else {
					result = and_w1(getRange(), t.getRange());
				}
			}
		}
		logger.debug(this + " & " + t + " = " + result);
		return result;
	}

	private static CongruenceClassInterval xor_w1(IntervalElement s, IntervalElement t) {
		// no information, so not much to do here
		return zeroInterval(s.xor(t));
	}

	private static CongruenceClassInterval xor_w2(IntervalElement range1, IntervalElement modRange1, BitNumber modulus1, IntervalElement range2, IntervalElement modRange2, BitNumber modulus2) {
		if (modulus1.log2n().hasValue()) {
			if (modulus1.equals(modulus2)) {
				// same congruence and a power of two. so we compute the bitwise xor everywhere and are done
				return modInterval(range1.xor(range2), modRange1.xor(modRange2), modulus1);
			} else if (modulus2.log2n().hasValue()) {
				// different congruences, but powers of two. extend the ranges.
				BitNumber m = modulus1.uMax(modulus2);
				return modInterval(range1.xor(range2), extendBitRange(modRange1, modulus1, m).xor(extendBitRange(modRange2, modulus2, m)), m);
			}
		}
		// drop useless information
		return xor_w1(range1, range2);
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> xor(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD && t.kind == CCIntervalKind.MOD) {
			result = xor_w2(range, modRange, modulus, t.range, t.modRange, t.modulus);
		} else {
			result = xor_w1(getRange(), t.getRange());
		}
		logger.debug(this + " ^ " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> not() {
		return add(number(BitNumber.valueOf(1L, bitSize))).negate();
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> cast(int bitSize) {
		if (bitSize > this.bitSize) {
			return zeroExtend(bitSize);
		} else {
			return truncate(bitSize);
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> signExtend(int firstBit, int lastBit) {
		assert firstBit > 0 && firstBit <= 64 && firstBit <= lastBit : "Invalid first bit " + firstBit;
		assert lastBit > 0 && lastBit <= 64 : "Invalid last bit " + lastBit;
		int targetWidth = Math.max(bitSize, lastBit + 1);
		CongruenceClassInterval result = signExtend(targetWidth).abstractGet();
		if (firstBit - 1 == bitSize) {
			return result;
		} else {
			// this looks kinda fishy... so lets fail for the moment, change this similar to the IntervalElement method if
			// this is a valid case.
			throw new IllegalArgumentException("Strange sign extension: " + firstBit + " to " + lastBit + " for " + this);
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> signExtend(int bitSize) {
		assert bitSize > this.bitSize;
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			List<CongruenceClassInterval> xs = new ArrayList<>();
			for (IntervalElement x : range.cut()) {
				assert x.isInterval();
				if (x.minBits.msb() && x.maxBits.msb()) {
					xs.add(modInterval(x.signExtend(bitSize), modRange.cast(bitSize), modulus.zExtend(bitSize)));
				} else {
					assert !x.minBits.msb();
					assert !x.maxBits.msb();
					BigInteger c = IntervalElement.maxIntervalSize(bitSize).subtract(range.maxIntervalSize());
					BitNumber d = BitNumber.valueOf(c.longValue(), bitSize);
					xs.add(modInterval(x.cast(bitSize), modRange.cast(bitSize), modulus.zExtend(bitSize)).add(number(d)).abstractGet());
				}
			}
			result = joinsCC(bitSize, xs);
		} else {
			result = modInterval(getRange().signExtend(bitSize), getRange().cast(bitSize), BitNumber.valueOf(getRange().maxIntervalSize().longValue(), bitSize));
		}
		logger.debug("sign-extend " + this + " to " + bitSize + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> zeroExtend(int firstBit, int lastBit) {
		assert firstBit > 0 && firstBit <= 64 && firstBit <= lastBit : "Invalid first bit " + firstBit;
		assert lastBit > 0 && lastBit <= 64 : "Invalid last bit " + lastBit;
		int targetWidth = Math.max(bitSize, lastBit + 1);
		CongruenceClassInterval result = zeroExtend(targetWidth).abstractGet();
		if (firstBit - 1 == bitSize) {
			return result;
		} else {
			// this looks kinda fishy... so lets fail for the moment, remove the assert if this is a valid case...
			assert false : "Strange zero extension: " + firstBit + " to " + lastBit + " for " + this;
			// keep only the bits from 0..firstBit-1 and lastBit+1 .. targetWidth-1, as the other bits
			// should get set to 0 from the extension.
			return result.and(number(bitMask(0, firstBit - 1) | bitMask(lastBit + 1, targetWidth - 1)));
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> zeroExtend(int bitSize) {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			result = modInterval(range.zeroExtend(bitSize), modRange.cast(bitSize), modulus.zExtend(bitSize));
		} else {
			result = modInterval(getRange().zeroExtend(bitSize), getRange().cast(bitSize), BitNumber.valueOf(getRange().maxIntervalSize().longValue(), bitSize));
		}
		logger.debug("zero-extend " + this + " to " + bitSize + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> truncate(int bitSize) {
		assert bitSize < this.bitSize;
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD) {
			IntervalElement s = range.truncate(bitSize);
			if (modulus.log2n().hasValue()) {
				BitNumber h = BitNumber.uMaxVal(bitSize).zExtend(this.bitSize).inc();
				if (modulus.ult(h)) {
					result = modInterval(s, modRange.truncate(bitSize), modulus.trunc(bitSize));
				} else if (modulus.equals(h) || modulus.urem(h).zExtLongValue() == 0L) {
					result = zeroInterval(s.joinIntersections(modRange.truncate(bitSize)));
				} else {
					result = zeroInterval(s);
				}
			} else {
				result = zeroInterval(s);
			}
		} else {
			result = zeroInterval(getRange().truncate(bitSize));
		}
		logger.debug("truncate " + this + " to " + bitSize + " = " + result);
		return result;
	}

	/**
	 * Join multiple cc-intervals at once.
	 *
	 * @param bitSize Bitsize of all intervals.
	 * @param c Collection of all intervals.
	 * @return The result.
	 */
	static CongruenceClassInterval joinsCC(int bitSize, Collection<CongruenceClassInterval> c) {
		CongruenceClassInterval acc = bot(bitSize);
		for (CongruenceClassInterval x : c) {
			assert bitSize == x.getBitWidth();
			acc = acc.join(x);
		}
		if (!acc.isBot() && !acc.isTop()) {
			List<IntervalElement> tmp = new ArrayList<>(c.size());
			for (CongruenceClassInterval x : c) {
				tmp.add(x.getRange());
			}
			if (acc.kind == CCIntervalKind.ZERO) {
				acc = zeroInterval(IntervalElement.smaller(acc.range, IntervalElement.joins(bitSize, tmp)));
			} else {
				assert acc.kind == CCIntervalKind.MOD;
				acc = modInterval(IntervalElement.smaller(acc.range, IntervalElement.joins(bitSize, tmp)), acc.modRange, acc.modulus);
			}
		}
		for (CongruenceClassInterval x : c) {
			assert x.lessOrEqual(acc);
		}
		return acc;
	}

	/**
	 * Return the number of possible shift amounts and whether illegal shifts are possible.
	 *
	 * @return The result.
	 */
	private Pair<List<BitNumber>, Boolean> getShiftInfo() {
		if (isTop()) {
			List<BitNumber> xs = new ArrayList<>();
			for (long x = 0L; x < (long)bitSize; x++) {
				xs.add(BitNumber.valueOf(x, bitSize));
			}
			return new Pair<>(xs, Boolean.TRUE);
		} else if (isBot()) {
			return new Pair<>(Collections.<BitNumber>emptyList(), Boolean.FALSE);
		} else if (kind == CCIntervalKind.ZERO) {
			IntervalElement x = interval(BitNumber.valueOf(0L, bitSize), BitNumber.valueOf((long)bitSize - 1L, bitSize));
			IntervalElement y = x.invert();
			List<BitNumber> xs = new ArrayList<>();
			for (IntervalElement k : x.intersection(range)) {
				for (BitNumber l : k) {
					xs.add(l);
				}
			}
			return new Pair<>(xs, y.intersection(range).length != 0);
		} else {
			assert kind == CCIntervalKind.MOD;
			IntervalElement x = interval(BitNumber.valueOf(0L, bitSize), BitNumber.valueOf((long)bitSize - 1L, bitSize));
			IntervalElement y = x.invert();
			List<BitNumber> xs = new ArrayList<>();
			for (IntervalElement k : x.intersection(range)) {
				for (BitNumber l : k) {
					if (hasElement(l)) {
						xs.add(l);
					}
				}
			}
			return new Pair<>(xs, !modInterval(IntervalElement.joins(bitSize, Arrays.asList(y.intersection(range))), modRange, modulus).isBot());
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> shl(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (t.hasUniqueConcretization()) {
			BitNumber n = t.getUniqueConcretization();
			if (n.ult(BitNumber.valueOf((long)bitSize, bitSize))) {
				result = mul(number(BitNumber.valueOf(BitNumber.bit((int)n.zExtLongValue()), bitSize))).abstractGet();
			} else {
				result = number(BitNumber.valueOf(0L, bitSize));
			}
		} else {
			Pair<List<BitNumber>, Boolean> tmp = t.getShiftInfo();
			List<CongruenceClassInterval> xs = new ArrayList<>();
			if (tmp.getRight()) {
				xs.add(number(BitNumber.valueOf(0L, bitSize)));
			}
			for (BitNumber x : tmp.getLeft()) {
				xs.add(shl(number(x)).abstractGet());
			}
			result = joinsCC(bitSize, xs);
		}
		logger.debug(this + " << " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> shr(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (t.hasUniqueConcretization()) {
			BitNumber n = t.getUniqueConcretization();
			if (n.ult(BitNumber.valueOf((long)bitSize, bitSize))) {
				result = zeroInterval(getRange().shr(IntervalElement.number(n)));
			} else {
				result = number(BitNumber.valueOf(0L, bitSize));
			}
		} else {
			Pair<List<BitNumber>, Boolean> tmp = t.getShiftInfo();
			List<CongruenceClassInterval> xs = new ArrayList<>();
			if (tmp.getRight()) {
				xs.add(number(BitNumber.valueOf(0L, bitSize)));
			}
			for (BitNumber x : tmp.getLeft()) {
				xs.add(shr(number(x)).abstractGet());
			}
			result = joinsCC(bitSize, xs);
		}
		logger.debug(this + " >>> " + t + " = " + result);
		return result;
	}

	/**
	 * Determine the result of a shift arithmetic right by an illegal amount.
	 *
	 * @return The result.
	 */
	private CongruenceClassInterval sarResult() {
		BitNumber z = BitNumber.valueOf(0L, bitSize);
		if (isTop()) {
			return number(z).join(number(z.not()));
		} else if (isBot()) {
			return this;
		} else {
			boolean includesPlus = range.intersection(interval(range.southPoleEnd(), range.northPoleStart())).length != 0;
			boolean includesMinus = range.intersection(interval(range.northPoleEnd(), range.southPoleStart())).length != 0;
			CongruenceClassInterval r = includesPlus ? number(z) : bot();
			if (includesMinus) {
				r.join(number(z.not()));
			}
			return r;
		}
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> sar(CongruenceClassInterval t) {
		final CongruenceClassInterval result;

		if (t.hasUniqueConcretization()) {
			BitNumber n = t.getUniqueConcretization();
			if (n.ult(BitNumber.valueOf((long)bitSize, bitSize))) {
				result = zeroInterval(getRange().sar(IntervalElement.number(n)));
			} else {
				result = sarResult();
			}
		} else {
			Pair<List<BitNumber>, Boolean> tmp = t.getShiftInfo();
			List<CongruenceClassInterval> xs = new ArrayList<>();
			if (tmp.getRight()) {
				xs.add(sarResult());
			}
			for (BitNumber x : tmp.getLeft()) {
				xs.add(shr(number(x)).abstractGet());
			}
			result = joinsCC(bitSize, xs);
		}

		logger.debug(this + " >> " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> eq(CongruenceClassInterval t) {
		final CongruenceClassInterval result;
		if (kind == CCIntervalKind.MOD && t.kind == CCIntervalKind.MOD) {
			if (range.intersection(t.range).length == 0) {
				result = FALSE_CC_INTERVAL;
			} else if (modulus.equals(t.modulus)) {
				if (modRange.intersection(t.modRange).length == 0) {
					result = FALSE_CC_INTERVAL;
				} else {
					result = zeroInterval(getRange().eq(t.getRange()));
				}
			} else {
				BitNumber m = modulus.gcd(t.modulus);
				if (m.equals(m.valueOf(1L)) || modRange.num_rem_cc(m).intersection(t.modRange.num_rem_cc(m)).length != 0) {
					result = zeroInterval(getRange().eq(t.getRange()));
				} else {
					result = FALSE_CC_INTERVAL;
				}
			}
		} else {
			result = zeroInterval(getRange().eq(t.getRange()));
		}
		logger.debug(this + " == " + t + " = " + result);
		return result;
	}

	private IntervalElement getRange() {
		if (isTop()) {
			assert range == null;
			return IntervalElement.top(bitSize);
		} else if (isBot()) {
			assert range == null;
			return IntervalElement.bot(bitSize);
		} else {
			assert range != null;
			return range;
		}
	}

	// these operations only concern themselves with bounds, so we ignore congruence information

	@Override
	public AbstractDomain<CongruenceClassInterval> signedLessThan(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().signedLessThan(t.getRange()));
		logger.debug(this + " <_s " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> signedLessThanOrEqual(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().signedLessThanOrEqual(t.getRange()));
		logger.debug(this + " <=_s " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> unsignedLessThan(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().unsignedLessThan(t.getRange()));
		logger.debug(this + " <_u " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> unsignedLessThanOrEqual(CongruenceClassInterval t) {
		CongruenceClassInterval result = zeroInterval(getRange().unsignedLessThanOrEqual(t.getRange()));
		logger.debug(this + " <=_u " + t + " = " + result);
		return result;
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> widen(CongruenceClassInterval t) {
		// TODO widen
		if (kind == CCIntervalKind.MOD && t.kind == CCIntervalKind.MOD) {
			return modInterval(range.widen(t.range), modRange.widen(t.modRange), modulus.gcd(t.modulus));
		} else {
			return zeroInterval(getRange().widen(t.getRange()));
		}
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
		} else if (kind == CCIntervalKind.ZERO) {
			return range.getIdentifier();
		} else {
			return range.toString() + '(' + modRange + '[' + modulus + "])";
		}
	}

	@Override
	public int getBitWidth() {
		return bitSize;
	}

	@Override
	public String toString() {
		return getIdentifier();
	}

	@Override
	public boolean equals(Object obj) {
		if (obj instanceof CongruenceClassInterval) {
			CongruenceClassInterval t = (CongruenceClassInterval) obj;
			if (isTop() || isBot()) {
				return kind == t.kind;
			} else if (kind == CCIntervalKind.ZERO) {
				return kind == t.kind && range.equals(t.range);
			} else {
				return kind == t.kind && range.equals(t.range) && modRange.equals(t.modRange) && modulus.equals(t.modulus);
			}
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		if (isTop() || isBot()) {
			return kind.hashCode();
		} else if (kind == CCIntervalKind.ZERO) {
			return kind.hashCode() ^ range.hashCode();
		} else {
			return kind.hashCode() ^ range.hashCode() ^ modRange.hashCode() ^ modulus.hashCode();
		}
	}

	/**
	 * Create a new cc-interval.
	 *
	 * @param min Minimum allowed bit-pattern.
	 * @param max Maximum allowed bit-pattern.
	 * @return The result.
	 */
	public static CongruenceClassInterval ccInterval(BitNumber min, BitNumber max) {
		return getFromCache(zeroInterval(interval(min, max)));
	}

	@Override
	public AbstractDomain<CongruenceClassInterval> abstractBox() {
		return this;
	}

	enum RevMode {
		M1, M2, M3
	}

	/**
	 * Join a collection of intervals in a range (i.e. including values outside of the range is considered free).
	 *
	 * @param range Range to join values in.
	 * @param xs Values.
	 * @return An interval containing all intervals in xs.
	 */
	private static IntervalElement joinsInRange(IntervalElement range, Collection<IntervalElement> xs) {
		for (IntervalElement x : xs) {
			assert range.getBitWidth() == x.getBitWidth();
		}
		if (range.isTop()) {
			return IntervalElement.joins(range.getBitWidth(), xs);
		} else if (range.isBot()) {
			return range; // bot
 		} else {
			List<IntervalElement> acc = new ArrayList<>();
			for (IntervalElement x : xs) {
				assert range.getBitWidth() == x.getBitWidth();
				if (x.isBot()) {
					continue;
				}
				if (x.isTop()) {
					return range;
				}
				assert x.minBits.uleq(x.maxBits) && x.lessOrEqual(range) : "joinsInRange failed: " + range + ' ' + acc + ' ' + x + ' ' + xs;
				acc.add(x);
			}
			if (acc.isEmpty()){
				return range.bot();
			} else {
				assert acc.get(0).isInterval();
				BitNumber c = acc.get(0).minBits;
				BitNumber d = acc.get(0).maxBits;
				RevMode mode;
				if (range.minBits.uleq(range.maxBits)) {
					for (IntervalElement x : acc) {
						assert x.isInterval();
						c = c.uMin(x.minBits);
						d = d.uMax(x.maxBits);
					}
					return interval(c, d);
				} else if (d.uleq(range.maxBits)) {
					mode = M1;
				} else {
					mode = M2;
				}
				for (int pos = 1; pos < acc.size(); pos++) {
					assert acc.get(pos).isInterval();
					BitNumber e = acc.get(pos).minBits;
					BitNumber f = acc.get(pos).maxBits;
					if (mode == M3) {
						if (f.uleq(range.maxBits)) {
							d = d.uMax(f);
						} else {
							c = c.uMin(e);
						}
					} else {
						if (mode == M1 && f.ugt(range.maxBits)) {
							mode = M3;
							c = e;
							continue;
						}
						if (mode == M2 && f.uleq(range.maxBits)) {
							mode = M3;
							d = f;
							continue;
						}
						c = c.uMin(e);
						d = d.uMax(f);
					}
				}
				return interval(c, d);
			}
		}
	}

	private static IntervalElement constrainModRangeWithRange(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		List<IntervalElement> xs = new ArrayList<>();
		for (IntervalElement r : range.num_rem_w(modulus)) {
			Collections.addAll(xs, r.intersection(modRange));
		}
		IntervalElement result = joinsInRange(modRange, xs);
		logger.debug("constrainModRangeWithRange " + range + ' ' + modRange + ' ' + modulus + " = " + result);
		return result;
	}

	private static IntervalElement constrainRange(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		assert range.getBitWidth() == modRange.getBitWidth();
		assert range.getBitWidth() == modulus.getBitWidth();

		final IntervalElement result;
		if (range.isBot()) {
			result = range; // bot
		} else if (range.isTop()) {
			if (modRange.isTop()) {
				result = range; // top
			} else if (modRange.isBot()) {
				result = modRange; // bot
			} else {
				Optional<BitNumber> maxBound = findMaxBound(modulus.uMaxVal(), modRange, modulus);
				if (maxBound.hasValue()) {
					result = interval(modRange.intervalMin(), maxBound.getValue());
				} else {
					result = range.bot();
				}
			}
		} else {
			if (modRange.isTop()) {
				result = range;
			} else if (modRange.isBot()) {
				result = modRange; // bot
			} else {
				Optional<BitNumber> minBound = findMinBound(range.minBits, modRange, modulus);
				Optional<BitNumber> maxBound = findMaxBound(range.maxBits, modRange, modulus);
				if (range.maxBits.ult(range.minBits)) {
					if (minBound.hasValue() && maxBound.hasValue()) {
						result = interval(minBound.getValue(), maxBound.getValue());
					} else {
						List<IntervalElement> tmp = new ArrayList<>();
						for (IntervalElement y : range.splitSouth()) {
							IntervalElement x = constrainRange(y, modRange, modulus);
							if (!x.isBot()) {
								tmp.add(x);
							}
						}
						result = IntervalElement.joins(range.getBitWidth(), tmp);
					}
				} else {
					if (minBound.hasValue() && maxBound.hasValue() && maxBound.getValue().ugeq(minBound.getValue())) {
						result = interval(minBound.getValue(), maxBound.getValue());
					} else {
						result = range.bot();
					}
				}
			}
		}
		logger.debug("constrainRange " + range + ' ' + modRange + ' ' + modulus + " = " + result);
		assert result.lessOrEqual(range);
		return result;
	}

	private static Optional<BitNumber> findMaxBound(BitNumber maxPos, IntervalElement t, BitNumber m) {
		assert maxPos.getBitWidth() == t.getBitWidth();
		assert t.getBitWidth() == m.getBitWidth();

		final Optional<BitNumber> result;
		BitNumber remVal = maxPos.urem(m);
		BitNumber nextBase = remVal.add(m);

		if (t.hasElement(remVal)) {
			result = new Optional<>(maxPos);
		} else {
			Optional<BitNumber> u = t.nextLowerOrEqual(remVal);
			if (u.hasValue()) {
				result = new Optional<>(maxPos.sub(remVal).add(u.getValue()));
			} else {
				Optional<BitNumber> v = t.nextLowerOrEqual(nextBase);
				BigInteger maxVal = maxPos.uMaxVal().unsignedBigValue();
				BigInteger iRes = maxPos.unsignedBigValue().subtract(remVal.unsignedBigValue()).add(v.hasValue() ? v.getValue().unsignedBigValue() : BigInteger.ZERO).subtract(m.unsignedBigValue());
				if (v.hasValue() && iRes.compareTo(maxVal) < 1 && iRes.compareTo(BigInteger.ZERO) > -1) {
					result = new Optional<>(maxPos.sub(remVal).add(v.getValue()).sub(m));
				} else {
					result = Optional.none();
				}
			}
		}
		logger.debug("findMaxBound " + maxPos + ' ' + t + ' ' + m + " = " + result);
		if (result.hasValue()) {
			assert result.getValue().uleq(maxPos) : "findMaxBound: result did grow the bound";
			assert t.hasElement(result.getValue().urem(m)) : "findMaxBound: result not in mod-interval";
		}
		return result;
	}

	private static Optional<BitNumber> findMinBound(BitNumber minPos, IntervalElement t, BitNumber m) {
		assert minPos.getBitWidth() == t.getBitWidth();
		assert t.getBitWidth() == m.getBitWidth();

		final Optional<BitNumber> result;
		BitNumber x = minPos.urem(m);
		BitNumber b = minPos.sub(x);
		if (t.hasElement(x)) {
			result = new Optional<>(minPos);
		} else {
			Optional<BitNumber> u = t.nextUpperOrEqual(x);
			BigInteger maxVal = minPos.uMaxVal().unsignedBigValue();
			if (u.hasValue() && b.unsignedBigValue().add(u.getValue().unsignedBigValue()).compareTo(maxVal) < 1) {
				result = new Optional<>(b.add(u.getValue()));
			} else {
				BitNumber v = t.intervalMin();
				if (b.unsignedBigValue().add(v.unsignedBigValue()).add(m.unsignedBigValue()).compareTo(maxVal) < 1) {
					result = new Optional<>(b.add(v).add(m));
				} else {
					result = Optional.none();
				}
			}
		}
		logger.debug("findMinBound " + minPos + ' ' + t + ' ' + m + " = " + result);
		if (result.hasValue()) {
			assert result.getValue().ugeq(minPos) : "findMinBound: result did shrink the bound";
			assert t.hasElement(result.getValue().urem(m)) : "findMinBound: result not in mod-interval";
		}
		return result;
	}

	private static class ConstructorResult {
		final IntervalElement range;
		final IntervalElement modRange;
		final BitNumber modulus;
		final CCIntervalKind kind;

		ConstructorResult(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
			this.range = range;
			this.modRange = modRange;
			this.modulus = modulus;
			kind = CCIntervalKind.MOD;
		}

		ConstructorResult(IntervalElement range) {
			assert range != null && range.isInterval();
			this.range = range;
			modRange = null;
			modulus = null;
			kind = CCIntervalKind.ZERO;
		}

		ConstructorResult(CCIntervalKind kind) {
			assert kind == CCIntervalKind.BOT || kind == CCIntervalKind.TOP;
			range = null;
			modRange = null;
			modulus = null;
			this.kind = kind;
		}
	}

	private static ConstructorResult mkCCInterval(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		if (range.isBot() || modRange.isBot()) {
			return new ConstructorResult(CCIntervalKind.BOT);
		} else if (modulus.zExtLongValue() == 1L) {
			if (modRange.hasElement(modulus.valueOf(0L))) {
				return new ConstructorResult(range);
			} else {
				return new ConstructorResult(CCIntervalKind.BOT);
			}
		} else if (modRange.isTop()) {
			return new ConstructorResult(range);
		} else if (range.isTop()) {
			modRange = constrainModRange(modRange, modulus);
			if (modRange.isBot()) {
				return new ConstructorResult(CCIntervalKind.BOT);
			} else if (modRange.isTop() || modRange.minBits.zExtLongValue() == 0L && modRange.maxBits.zExtLongValue() == modulus.zExtLongValue() - 1L) {
				return new ConstructorResult(CCIntervalKind.TOP);
			} else {
				range = constrainRange(range, modRange, modulus);
				if (range.isBot()) {
					return new ConstructorResult(CCIntervalKind.BOT);
				} else if (range.hasUniqueConcretization()) {
					return new ConstructorResult(range);
				} else {
					return ccMkModInterval(range, modRange, modulus);
				}
			}

		} else {
			modRange = constrainModRange(modRange, modulus);
			if (modRange.isBot()) {
				return new ConstructorResult(CCIntervalKind.BOT);
			} else if (modRange.isTop() || modRange.maxBits.equals(modulus.dec())) {
				return new ConstructorResult(range);
			} else {
				range = constrainRange(range, modRange, modulus);
				if (range.isBot()) {
					return new ConstructorResult(CCIntervalKind.BOT);
				} else if (range.hasUniqueConcretization()) {
					return new ConstructorResult(range);
				} else {
					return ccMkModInterval(range, modRange, modulus);
				}
			}
		}
	}

	private static ConstructorResult ccMkModInterval(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		if (range.lessOrEqual(interval(modulus.valueOf(0L), modulus.dec()))) {
			IntervalElement[] tmp = range.intersection(modRange);
			if (tmp.length == 0) {
				return new ConstructorResult(CCIntervalKind.BOT);
			} else if (tmp.length == 1) {
				return new ConstructorResult(tmp[0]);
			} else {
				return ccMkModInterval2(range, modRange, modulus);
			}
		} else {
			return ccMkModInterval2(range, modRange, modulus);
		}
	}

	private static ConstructorResult ccMkModInterval2(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		List<IntervalElement> xs = range.num_rem_w(modulus);
		boolean allSubset = true;
		for (IntervalElement x : xs) {
			allSubset &= x.lessOrEqual(modRange);
		}
		if (allSubset) {
			IntervalElement x = joinsInRange(modRange, xs);
			if (x.isTop()) {
				return new ConstructorResult(range, modRange, modulus);
			} else if (x.isBot()) {
				return new ConstructorResult(CCIntervalKind.BOT);
			} else {
				BitNumber l = x.minBits.urem(modulus);
				IntervalElement tmp = interval(l, x.maxBits.sub(x.minBits).add(l).urem(modulus));
				if (tmp.equals(modRange)) {
					return new ConstructorResult(range);
				}
				// otherwise fall through
			}
		}
		IntervalElement t = constrainModRangeWithRange(range, modRange, modulus);
		if (t.equals(modRange)) {
			return new ConstructorResult(range, modRange, modulus);
		} else {
			return mkCCInterval(range, t, modulus);
		}
	}

	private CongruenceClassInterval(IntervalElement range, IntervalElement modRange, BitNumber modulus) {
		assert range.getBitWidth() == modRange.getBitWidth();
		assert range.getBitWidth() == modulus.getBitWidth();
		assert modulus.zExtLongValue() != 0L;

		ConstructorResult r = mkCCInterval(range, modRange, modulus);
		this.range = r.range;
		this.modRange = r.modRange;
		this.modulus = r.modulus;
		kind = r.kind;
		bitSize = range.getBitWidth();

		Statistic.countCCIntervalElementCreate();
		logger.debug("Created new cc-interval " + this);
	}

	/**
	 * Create a new top cc-interval of the given bitsize.
	 *
	 * @param bitSize The bitsize.
	 * @return The new top cc-interval.
	 */
	public static CongruenceClassInterval top(int bitSize) {
		return getFromCache(new CongruenceClassInterval(bitSize, CCIntervalKind.TOP));
	}

	/**
	 * Create a new top cc-interval of the current bitsize.
	 *
	 * @return The new top cc-interval.
	 */
	public CongruenceClassInterval top() {
		return top(bitSize);
	}

	/**
	 * Create a new bot cc-interval of the given bitsize.
	 *
	 * @param bitSize The bitsize.
	 * @return The new bot cc-interval.
	 */
	public static CongruenceClassInterval bot(int bitSize) {
		return getFromCache(new CongruenceClassInterval(bitSize, CCIntervalKind.BOT));
	}

	/**
	 * Create a new bot cc-interval of the current bitsize.
	 *
	 * @return The new bot cc-interval.
	 */
	public CongruenceClassInterval bot() {
		return bot(bitSize);
	}

	private enum CCIntervalKind {
		TOP, // all numbers are valid
		BOT, // no number is valid
		ZERO, // no congruence information
		MOD // congruence information
	}
}
