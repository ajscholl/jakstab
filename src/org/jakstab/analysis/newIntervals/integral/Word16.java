package org.jakstab.analysis.newIntervals.integral;

public class Word16 extends Word<Word16> implements Integral<Word16> {

	public Word16(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 0xFFFF;
	}

	@Override
	public Word16 mkThis(long val) {
		return new Word16(val);
	}

	@Override
	public long longValue() {
		short v = (short)val;
		return (long)v;
	}
}
