package org.jakstab.analysis.newIntervals;

import org.jakstab.analysis.AbstractState;
import org.jakstab.analysis.AbstractValue;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.Precision;
import org.jakstab.cfa.Location;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.FastSet;
import org.jakstab.util.Logger;
import org.jakstab.util.Sets;
import org.jakstab.util.Tuple;

import java.math.BigDecimal;
import java.util.*;

public class Interval implements Comparable<Interval>, AbstractState, AbstractValue {

	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);

    private final long minBits;
    private final long maxBits;
    private final Bits bits;
    private final IntervalKind kind;

	private static final Interval undefInterval = new Interval(0, 0, Bits.BIT0, IntervalKind.UNDEF);
	private static final EnumMap<Bits, Interval> botIntervals = new EnumMap<>(Bits.class);
	private static final EnumMap<Bits, Interval> topIntervals = new EnumMap<>(Bits.class);

    private Interval (long minBits, long maxBits, Bits bits, IntervalKind kind) {
        assert bits != null;
        assert kind != null;

        this.minBits = minBits;
        this.maxBits = maxBits;
        this.bits = bits;
        this.kind = kind;
    }

	public static Interval mkDefaultInterval() {
		return undefInterval;
	}

    public static Interval mkTopInterval(Bits bits) {
		Interval i = topIntervals.get(bits);
		if (i == null) {
			i = new Interval(0, 0, bits, IntervalKind.TOP);
			topIntervals.put(bits, i);
		}
        return i;
    }

    public static Interval mkBotInveral(Bits bits) {
		Interval i = botIntervals.get(bits);
		if (i == null) {
			i = new Interval(0, 0, bits, IntervalKind.BOT);
			botIntervals.put(bits, i);
		}
		return i;
    }

    private static Interval mkSomeInterval(long min, long max, Bits bits) {
        return new Interval(min & bits.getMask(), max & bits.getMask(), bits, IntervalKind.INTERVAL);
    }

    @Override
    public int compareTo(Interval t) {
        assert bits == t.bits;
        if (kind != t.kind) {
			return kind.compareTo(t.kind);
        } else if (kind == IntervalKind.INTERVAL) {
			return (minBits == t.minBits) ? Long.compare(maxBits, t.maxBits) : Long.compare(minBits, t.minBits);
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
        long h = minBits ^ maxBits;
		return kind.hashCode() ^ bits.hashCode() ^ (int)h ^ (int)(h >>> 32);
	}

	@Override
	public String toString() {
		return getIdentifier();
	}

	@Override
	public Set<RTLNumber> concretize() {
		if (isBot()) {
			return Collections.EMPTY_SET;
		}
		if (isTop()) {
			return RTLNumber.ALL_NUMBERS;
		}
		Set<RTLNumber> s = new FastSet<>();
		if (minBits <= maxBits) {
			for (long i = minBits; i <= maxBits; i++) {
				s.add(ExpressionFactory.createNumber(i, bits.getBits()));
			}
		} else {
			for (long i = 0; i <= minBits; i++) {
				s.add(ExpressionFactory.createNumber(i, bits.getBits()));
			}
			for (long i = maxBits; i != Long.MIN_VALUE; i++) {
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
		checkCompatible(t);
		if (kind == IntervalKind.UNDEF) {
			return t;
		}
		if (t.kind == IntervalKind.UNDEF) {
			return this;
		}

		if (isSubsetOf(t)) {
			return t;
		}
		if (t.isSubsetOf(this)) {
			return this;
		}
		if (t.isElement(minBits) && t.isElement(maxBits) && isElement(t.minBits) && isElement(t.maxBits)) {
			return mkTopInterval(bits);
		}
		if (t.isElement(maxBits) && isElement(t.minBits)) {
			return mkSomeInterval(minBits, t.maxBits, bits);
		}
		if (isElement(t.maxBits) && t.isElement(minBits)) {
			return mkSomeInterval(t.minBits, maxBits, bits);
		}
		BigDecimal r1 = internalSize(maxBits, t.minBits, bits);
		BigDecimal r2 = internalSize(t.maxBits, minBits, bits);
		int cmp = r1.compareTo(r2);
		if (cmp < 0 || cmp == 0 && minBits <= t.minBits) {
			return mkSomeInterval(minBits, t.maxBits, bits);
		}
		return mkSomeInterval(t.minBits, maxBits, bits);
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		return isSubsetOf((Interval)l);
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
		Tuple<Set<RTLNumber>> cValues = new Tuple<Set<RTLNumber>>(expressions.length);
		for (int i=0; i<expressions.length; i++) {
			Interval aValue = abstractEval(expressions[i]);
			logger.debug("expression: " + expressions[i] + " evalutated to: " + aValue + " " + aValue.isTop());
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
     * @return The number of elements in the interval. It can be larger than a long, so it is returned as a BigDecimal.
     */
    public BigDecimal size() {
		if (isTop()) {
			return BigDecimal.valueOf(2).pow(bits.getBits());
		} else if (isBot()) {
			return BigDecimal.ZERO;
		} else {
			return internalSize(minBits, maxBits, bits);
		}
    }

    private static BigDecimal internalSize(long min, long max, Bits bits) {
        long v = bits.add(bits.sub(max, min), 1);
        if (v >= 0) {
            return BigDecimal.valueOf(v);
        } else {
            return BigDecimal.valueOf(v).add(BigDecimal.valueOf(2).pow(bits.getBits()));
        }
    }

    /**
     * Invert this interval.
     */
    public Interval invert() {
        switch (kind) {
            case BOT: return mkTopInterval(bits);
            case TOP: return mkBotInveral(bits);
			case UNDEF: return this;
            default: return mkSomeInterval(bits.add(maxBits, 1), bits.sub(minBits, 1), bits);
        }
    }

    /**
     * Check if a value is in the interval.
     * @param e The value.
     * @return True if the value is in the interval.
     */
    public boolean isElement(long e) {
		return isTop() || !isBot() && bits.leq(minBits, e, maxBits);
	}

	/**
	 * Check if the given interval is compatible with the current one.
	 * @param t The interval to check.
	 */
	private void checkCompatible(Interval t) {
		assert bits == t.bits || kind == IntervalKind.UNDEF || t.kind == IntervalKind.UNDEF;
	}

    /**
     * Check if an interval is a subinterval of this interval.
     * @param t The interval to check.
     * @return True if the interval is a subinterval.
     */
    public boolean isSubsetOf(Interval t) {
		checkCompatible(t);
		return isBot() || t.isTop() ||
				!(isTop() || t.isBot()) &&
						t.isElement(minBits) && t.isElement(maxBits) &&
						(!isElement(t.minBits) || !isElement(t.maxBits));
	}

    private Interval pseudoMeet(Interval t) {
        return ((Interval)(invert().join(t.invert()))).invert();
    }

    private Interval gap(Interval t) {
        checkCompatible(t);
        if (!t.isElement(maxBits) && !isElement(t.minBits)) {
            return mkSomeInterval(t.minBits, maxBits, bits).invert();
        } else {
            return mkBotInveral(bits);
        }
    }

    private Interval extent(Interval t) {
		checkCompatible(t);
        if (isSubsetOf(t)) {
            return t;
        }
        if (t.isSubsetOf(this)) {
            return this;
        }
        if (t.isElement(minBits) && t.isElement(maxBits) && isElement(t.minBits) && isElement(t.maxBits)) {
            return mkTopInterval(bits);
        }
        if (t.isElement(maxBits) && isElement(t.minBits)) {
            return mkSomeInterval(minBits, t.maxBits, bits);
        }
        if (isElement(t.maxBits) && t.isElement(minBits)) {
			return mkSomeInterval(t.minBits, maxBits, bits);
        }
		return mkSomeInterval(minBits, t.maxBits, bits);
    }

    private static Interval bigger(Interval s, Interval t) {
		s.checkCompatible(t);
        return t.size().compareTo(s.size()) > 0 ? t : s;
    }

    public static Interval joins(Collection<Interval> c) {
        ArrayList<Interval> s = new ArrayList<>(c.size());
        for (Interval e : c) {
            s.add(e);
        }
        Collections.sort(s);
        Bits bits = s.iterator().next().bits;
        Interval f = mkBotInveral(bits);
        Interval g = mkBotInveral(bits);
        for (Interval e : s) {
            if (e.kind == IntervalKind.TOP || e.kind == IntervalKind.INTERVAL && bits.leq(0, e.maxBits, e.minBits)) {
                f.extent(e);
            }
        }
        for (Interval e : s) {
            g = bigger(g, f.gap(e));
            f.extent(e);
        }
        return bigger(f, g);
    }

	public Interval widen(Interval other) {
		checkCompatible(other);
		// TODO: this is really weak
		return mkTopInterval(bits);
	}

    public Interval addInterval(Interval t) {
        checkCompatible(t);
        if (isBot() || t.isBot()) {
            return mkBotInveral(bits);
        }
        if (size().add(t.size()).compareTo(BigDecimal.valueOf(2).pow(bits.getBits())) <= 0) {
            return mkSomeInterval(bits.add(minBits, t.minBits), bits.add(maxBits, t.maxBits), bits);
        }
        return mkTopInterval(bits);
    }

    public Interval subInterval(Interval t) {
		checkCompatible(t);
		if (isBot() || t.isBot()) {
			return mkBotInveral(bits);
		}
        if (size().add(t.size()).compareTo(BigDecimal.valueOf(2).pow(bits.getBits())) <= 0) {
			return mkSomeInterval(bits.sub(minBits, t.minBits), bits.sub(maxBits, t.maxBits), bits);
        }
		return mkTopInterval(bits);
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


	private Interval abstractEval(RTLExpression e) {
		final Bits bits = Bits.fromInt(e.getBitWidth());
		ExpressionVisitor<Interval> visitor = new ExpressionVisitor<Interval>() {

			@Override
			public Interval visit(RTLBitRange e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLConditionalExpression e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLMemoryLocation m) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLNondet e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLNumber e) {
				return mkSomeInterval(e.longValue(), e.longValue(), bits);
			}

			@Override
			public Interval visit(RTLOperation e) {
				return mkTopInterval(bits); //TODO
			}

			@Override
			public Interval visit(RTLSpecialExpression e) {
				return mkTopInterval(bits); //TODO
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
