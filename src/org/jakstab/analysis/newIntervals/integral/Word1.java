package org.jakstab.analysis.newIntervals.integral;

public class Word1 extends Word<Word1> implements Integral<Word1> {

	public Word1(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 1;
	}

	@Override
	public Word1 mkThis(long val) {
		return new Word1(val);
	}

	@Override
	public long longValue() {
		return val == 0 ? 0 : -1;
	}
}
