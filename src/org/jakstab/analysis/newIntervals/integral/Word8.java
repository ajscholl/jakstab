package org.jakstab.analysis.newIntervals.integral;

public class Word8 extends Word<Word8> implements Integral<Word8> {

	public Word8(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 0xFF;
	}

	@Override
	public Word8 mkThis(long val) {
		return new Word8(val);
	}

	@Override
	public long longValue() {
		byte v = (byte)val;
		return (long)v;
	}
}
