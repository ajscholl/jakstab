package org.jakstab.analysis.newIntervals;

import org.jakstab.Options;
import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.Precision;
import org.jakstab.analysis.newIntervals.word.Word;
import org.jakstab.analysis.newIntervals.word.Word64;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Sets;
import org.jakstab.util.Tuple;

import java.math.BigInteger;
import java.util.*;

public class Interval implements Comparable<Interval>, AbstractState, AbstractValue {

	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    private final Word minBits;
    private final Word maxBits;
    private final Bits bits;
    private final IntervalKind kind;

	private static final Interval undefInterval = new Interval(null, null, Bits.BIT0, IntervalKind.UNDEF);
	private static final EnumMap<Bits, Interval> botIntervals = new EnumMap<>(Bits.class);
	private static final EnumMap<Bits, Interval> topIntervals = new EnumMap<>(Bits.class);
	private static final Interval[] emptySet = new Interval[] {};

    private Interval (Word minBits, Word maxBits, Bits bits, IntervalKind kind) {
        assert bits != null;
        assert kind != null;

        this.minBits = minBits;
        this.maxBits = maxBits;
        this.bits = bits;
        this.kind = kind;
		logger.debug("Created new interval " + this);
    }

	public static Interval mkDefaultInterval() {
		return undefInterval;
	}

    public static Interval mkTopInterval(Bits bits) {
		Interval i = topIntervals.get(bits);
		if (i == null) {
			i = new Interval(null, null, bits, IntervalKind.TOP);
			topIntervals.put(bits, i);
		}
        return i;
    }

    public static Interval mkBotInterval(Bits bits) {
		Interval i = botIntervals.get(bits);
		if (i == null) {
			i = new Interval(null, null, bits, IntervalKind.BOT);
			botIntervals.put(bits, i);
		}
		return i;
    }

	private static Interval mkSomeInterval(long min, long max, Bits bits) {
		Word minW = Word.mkWord(min, bits);
		Word maxW = Word.mkWord(max, bits);
		return new Interval(minW, maxW, bits, IntervalKind.INTERVAL);
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
			return (minBits == t.minBits) ? maxBits.compareTo(t.maxBits) : minBits.compareTo(t.minBits);
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
	public Set<RTLNumber> concretize() {
		if (isBot()) {
			return Collections.emptySet();
		}
		if (isTop()) {
			return RTLNumber.ALL_NUMBERS;
		}
		Set<RTLNumber> s = new FastSet<>();
		if (minBits.lessThanOrEqual(maxBits)) {
			for (long i = minBits.unsafeInternalValue(); i <= maxBits.unsafeInternalValue(); i++) {
				s.add(ExpressionFactory.createNumber(i, bits.getBits()));
			}
		} else {
			for (long i = 0; i <= minBits.unsafeInternalValue(); i++) {
				s.add(ExpressionFactory.createNumber(i, bits.getBits()));
			}
			for (long i = maxBits.unsafeInternalValue(); i != Long.MIN_VALUE; i++) {
				s.add(ExpressionFactory.createNumber(i, bits.getBits()));
			}
		}
		return s;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return !isTop() && !isBot() && minBits == maxBits;
	}

	@Override
	public Interval join(LatticeElement l) {
		Interval t = (Interval) l;
		final Interval result;
		assertCompatible(t);
		if (kind == IntervalKind.UNDEF) {
			result = t;
		} else if (t.kind == IntervalKind.UNDEF) {
			result = this;
		} else if (lessOrEqual(t)) {
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
		return kind == IntervalKind.BOT || kind == IntervalKind.UNDEF;
	}

	@Override
	public Set<Tuple<RTLNumber>> projectionFromConcretization(RTLExpression... expressions) {
		logger.debug("projection from concretization for " + expressions.length + " expressions");
		Tuple<Set<RTLNumber>> cValues = new Tuple<>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			Interval aValue = abstractEval(expressions[i]);
			logger.debug("expression: " + expressions[i] + " evaluated to: " + aValue + " " + aValue.isTop());
			if(aValue.isTop()) {
				//is Boolean expression?
				if(expressions[i].getBitWidth() == 1)  {
					FastSet<RTLNumber> tmp = new FastSet<>(2);
					Collections.addAll(tmp, ExpressionFactory.TRUE, ExpressionFactory.FALSE);
					cValues.set(i, tmp);
				} else
					cValues.set(i, RTLNumber.ALL_NUMBERS);
			} else {
				//TODO limit up to k
				logger.debug("limit needed for: " + aValue + " with " + aValue.size() + " elements");
				cValues.set(i, aValue.concretize());
			}
		}
		return Sets.crossProduct(cValues);
	}

	@Override
	public Location getLocation() {
		throw new UnsupportedOperationException(this.getClass().getSimpleName() + " does not contain location information.");
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
     * @return The number of elements in the interval. It can be larger than a long, so it is returned as a BigInteger.
     */
    public BigInteger size() {
		final BigInteger size;
		if (isTop()) {
			size = BigInteger.valueOf(2).pow(bits.getBits());
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
			case UNDEF:
				logger.debug("Inverting undefined interval, result is still undefined!");
				result = this;
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
		assert bits.narrow(e) == e : "bad call to isElement with " + e + " (" + bits.narrow(e) + ", " + bits + ")";
		return isElement(Word.mkWord(e, bits));
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
		assert Word.mkWord(e, bits).equals(e);
		boolean result = isTop() || !isBot() && Bits.leq(minBits, e, maxBits);
		logger.debug(e + " element of " + this + ": " + result);
		return result;
	}

	/**
	 * Assert that the given interval is compatible with the current one.
	 *
	 * @param t The interval to check.
	 */
	private void assertCompatible(Interval t) {
		assert bits == t.bits || kind == IntervalKind.UNDEF || t.kind == IntervalKind.UNDEF;
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
			result = true;
		} else {
			result = t.isElement(minBits) && t.isElement(maxBits) && (!isElement(t.minBits) || !isElement(t.maxBits));
		}
		logger.debug(this + " is a subset of " + t + ": " + result);
		return result;
	}

    //private Interval meet(Interval t) {
    //    return (invert().join(t.invert())).invert();
    //}

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
        ArrayList<Interval> s = new ArrayList<>(c.size());
        for (Interval e : c) {
            s.add(e);
        }
        Collections.sort(s);
		logger.debug("** starting joins of " + s);
        Bits bits = s.iterator().next().bits;
        Interval f = mkBotInterval(bits);
        Interval g = mkBotInterval(bits);
        for (Interval e : s) {
            if (e.kind == IntervalKind.TOP || e.kind == IntervalKind.INTERVAL && Bits.leq(Word.mkWord(0, bits), e.maxBits, e.minBits)) {
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
			result = new Interval[] {t};
		} else if (t.isTop()) {
			result = new Interval[] {this};
		} else {
			boolean minInT = t.isElement(minBits);
			boolean maxInT = t.isElement(maxBits);
			boolean tMinInThis = isElement(t.minBits);
			boolean tMaxInThis = isElement((t.maxBits));
			if (minInT && maxInT && tMinInThis && tMaxInThis) {
				result = new Interval[] {mkSomeInterval(minBits, t.maxBits, bits), mkSomeInterval(maxBits, t.minBits, bits)};
			} else if (minInT && maxInT) {
				result = new Interval[] {this};
			} else if (tMinInThis && tMaxInThis) {
				result = new Interval[] {t};
			} else if (minInT && tMaxInThis) {
				result = new Interval[] {mkSomeInterval(minBits, t.maxBits, bits)};
			} else if (maxInT && tMinInThis) {
				result = new Interval[] {mkSomeInterval(maxBits, t.minBits, bits)};
			} else {
				result = emptySet;
			}
		}
		logger.debug("Intersection of " + this + " and " + t + " = " + Arrays.toString(result));
		return result;
	}

	private Interval getNorthPole() {
		assert bits != Bits.BIT0;
		long max = 1L << (bits.getBits() - 1L);
		long min = max - 1L;
		return mkSomeInterval(min, max, bits);
	}

	private Interval getSouthPole() {
		assert bits != Bits.BIT0;
		return mkSomeInterval(bits.getMask(), 0, bits);
	}

	/**
	 * Split an interval at the north pole.
	 *
	 * @return All sub-intervals.
	 */
	private Interval[] splitNorth() {
		assert bits != Bits.BIT0;
		final Interval[] result;
		if (isBot()) {
			result = emptySet;
		} else {
			long tmp = 1L << (bits.getBits() - 1L);
			if (isTop()) {
				result = new Interval[]{mkSomeInterval(0, tmp - 1L, bits), mkSomeInterval(tmp, bits.getMask(), bits)};
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
		assert bits != Bits.BIT0;
		final Interval[] result;
		if (isBot()) {
			result = emptySet;
		} else if (isTop()) {
			long tmp = 1L << (bits.getBits() - 1L);
			result =  new Interval[] {mkSomeInterval(0, tmp - 1L, bits), mkSomeInterval(tmp, bits.getMask(), bits)};
		} else if (!getSouthPole().isSubsetOf(this)) {
			result = new Interval[] {this};
		} else {
			result = new Interval[]{mkSomeInterval(0, maxBits.unsafeInternalValue(), bits), mkSomeInterval(minBits.unsafeInternalValue(), bits.getMask(), bits)};
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
				assert !Options.failFast.getValue().booleanValue() : "Extending 1-bit interval";
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
			default:
				assert !Options.failFast.getValue().booleanValue() : "Extending unknown interval size";
				return this;
		}
	}

	private Interval mul_u(Interval t) {
		assertCompatible(t);
		BigInteger a = minBits.bigValue();
		BigInteger b = maxBits.bigValue();
		BigInteger c = t.minBits.bigValue();
		BigInteger d = t.maxBits.bigValue();
		final Interval result;
		if (b.multiply(d).subtract(a.multiply(c)).compareTo(BigInteger.valueOf(2).pow(bits.getBits())) == -1) {
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
		BigInteger twoW = BigInteger.valueOf(2).pow(bits.getBits());
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

	public Interval widen(Interval t) {
		assertCompatible(t);
		final Interval result;
		if (isBot()) {
			result = t;
		} else if (t.isBot()) {
			result = this;
		} else if (isTop()) {
			result = this;
		} else if (t.isTop()) {
			result = t;
		} else if (t.lessOrEqual(this)) {
			result = this;
		} else if (size().compareTo(BigInteger.valueOf(2).pow(bits.getBits() - 1)) >= 0) {
			result = mkTopInterval(bits);
		} else {
			Interval tmp = join(t);
			Word one = Word.mkWord(1, bits);
			Word two = Word.mkWord(2, bits);
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

    public Interval addInterval(Interval t) {
        assertCompatible(t);
		final Interval result;
        if (isBot() || t.isBot()) {
            result = mkBotInterval(bits);
        } else if (isTop() || t.isTop()) {
			result = mkTopInterval(bits);
		} else if (size().add(t.size()).compareTo(BigInteger.valueOf(2).pow(bits.getBits())) <= 0) {
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
		} else if (size().add(t.size()).compareTo(BigInteger.valueOf(2).pow(bits.getBits())) <= 0) {
			result = mkSomeInterval(minBits.sub(t.minBits), maxBits.sub(t.maxBits), bits);
        } else {
			result = mkTopInterval(bits);
		}
		logger.debug(this + " - " + t + " = " + result);
		return result;
    }

	public Set<AbstractState> abstractPost(final RTLStatement statement, final Precision precision) {
		logger.verbose("start processing abstractPost(" + statement + ") " + statement.getLabel());

		Set<AbstractState> res = statement.accept(new DefaultStatementVisitor<Set<AbstractState>>() {

			@Override
			public Set<AbstractState> visit(RTLVariableAssignment stmt) {
				logger.verbose("Found RTLVariableAssignment: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLMemoryAssignment stmt) {
				logger.verbose("Found RTLMemoryAssignment: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLAssume stmt) {
				logger.verbose("Found RTLAssume: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLAlloc stmt) {
				logger.verbose("Found RTLAlloc: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLDealloc stmt) {
				logger.verbose("Found RTLDealloc: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLUnknownProcedureCall stmt) {
				logger.verbose("Found RTLUnknownProcedureCall: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLHavoc stmt) {
				logger.verbose("Found RTLHavoc: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLMemset stmt) {
				logger.verbose("Found RTLMemset: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visit(RTLMemcpy stmt) {
				logger.verbose("Found RTLMemcpy: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}

			@Override
			public Set<AbstractState> visitDefault(RTLStatement stmt) {
				logger.verbose("Found RTLStatement: " + stmt);
				return Collections.singleton((AbstractState)Interval.this); //TODO
			}
		});

		logger.debug("finished abstractPost(" + statement + ") in state: " + this + " with result: " + res);
		return res;
	}


	public static Interval abstractEval(RTLExpression e) {
		final Bits bits = Bits.fromInt(e.getBitWidth()); // TODO at least BitRanges explode sometimes...
		ExpressionVisitor<Interval> visitor = new ExpressionVisitor<Interval>() {

			@Override
			public Interval visit(RTLBitRange e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLConditionalExpression e) {
				Interval cond = abstractEval(e.getCondition());
				assert cond.bits == Bits.BIT1 : "Condition has to be a boolean";
				if (!cond.isTop() && cond.minBits == cond.maxBits) {
					if (cond.minBits.unsafeInternalValue() != 0) {
						assert cond.minBits.unsafeInternalValue() == 1;
						return abstractEval(e.getTrueExpression());
					}
					return abstractEval(e.getFalseExpression());
				} else {
					Interval t = abstractEval(e.getTrueExpression());
					Interval f = abstractEval(e.getFalseExpression());
					return t.join(f);
				}
			}

			@Override
			public Interval visit(RTLMemoryLocation m) {
				return mkTopInterval(bits); //TODO
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
				Interval e0, e1;
				switch (e.getOperator()) {
					case UNKNOWN:
						assert !Options.failFast.getValue() : "Evaluated unknown operator";
						return mkTopInterval(bits);

					// Operators for changing bit-width
					case CAST:
					case SIGN_EXTEND:
					case ZERO_FILL:
					case FSIZE:
						assert args.length == 1;
						e0 = abstractEval(args[0]);
						return mkTopInterval(bits); //TODO

					// Comparison
					case EQUAL:
					case LESS:
					case LESS_OR_EQUAL:
					case UNSIGNED_LESS:
					case UNSIGNED_LESS_OR_EQUAL:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return mkTopInterval(bits); //TODO

					// Unary operators
					case NOT:
						assert args.length == 1;
						e0 = abstractEval(args[0]);
						return mkTopInterval(bits); //TODO
					case NEG:
						assert args.length == 1;
						return mkSomeInterval(0, 0, bits).subInterval(abstractEval(args[0]));

					// Associative commutative bitwise arithmetic operators
					case AND:
					case OR:
					case XOR:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return mkTopInterval(bits); //TODO
					case PLUS:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return e0.addInterval(e1);
					case MUL:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return e0.mulInterval(e1);
					case FMUL:
					case FDIV:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return mkTopInterval(bits); //TODO

					// Other bitwise arithmetic operators
					case DIV:
					case MOD:
					case POWER_OF:
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return mkTopInterval(bits); //TODO

					// Bitwise shift operations
					case SHR:
					case SAR: /* Shift right with sign extension */
					case SHL:
					case ROL:
					case ROR:
					case ROLC:
					case RORC: /* Rotate with carry */
						assert args.length == 2;
						e0 = abstractEval(args[0]);
						e1 = abstractEval(args[1]);
						return mkTopInterval(bits); //TODO
					default:
						assert false : "Unknown operation";
						return null;
				}
			}

			@Override
			public Interval visit(RTLSpecialExpression e) {
				assert !Options.failFast.getValue() : "Evaluated special expression";
				return mkTopInterval(bits);
			}

			@Override
			public Interval visit(RTLVariable e) {
				return mkTopInterval(bits); //TODO
			}

		};

		Interval result = e.accept(visitor);

		logger.debug("abstractEval returned: " + result + " for " + e);

		return result;
	}

    /**
     * Different kinds of intervals.
     */
    public enum IntervalKind implements Comparable<IntervalKind> {
        TOP, INTERVAL, BOT, UNDEF
    }
}
