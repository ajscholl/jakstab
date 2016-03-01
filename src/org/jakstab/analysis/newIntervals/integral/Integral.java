package org.jakstab.analysis.newIntervals.integral;

public interface Integral<T> {
	T add(T b);
	T sub(T b);
	T mul(T b);
	T div(T b);
	T mod(T b);
	T inc();
	T dec();
	T shl(T b);
	T shr(T b);
	T and(T b);
	T or(T b);
	T xor(T b);
	T not();
	boolean lessThan(T b);
	boolean greaterThan(T b);
	boolean lessThanOrEqual(T b);
	boolean greaterThanOrEqual(T b);
	boolean equalTo(T b);
	boolean unequalTo(T b);
}
