package org.jakstab.analysis.newIntervals.word;

import java.util.HashMap;

public class Word8 extends Word {

	private static HashMap<Long, Word> cache = new HashMap<>();

	public Word8(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 0xFF;
	}

	@Override
	public Word mkThis(long val) {
		return new Word8(val);
	}

	@Override
	protected HashMap<Long, Word> getCache() {
		return cache;
	}

	@Override
	public long longValue() {
		byte v = (byte)val;
		return (long)v;
	}
}
