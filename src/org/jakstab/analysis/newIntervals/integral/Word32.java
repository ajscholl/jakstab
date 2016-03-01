package org.jakstab.analysis.newIntervals.integral;

public class Word32 extends Word<Word32> implements Integral<Word32> {

	public Word32(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 0xFFFFFFFF;
	}

	@Override
	public Word32 mkThis(long val) {
		return new Word32(val);
	}

	@Override
	public long longValue() {
		int v = (int)val;
		return (long)v;
	}
}
