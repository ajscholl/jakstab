package org.jakstab.analysis.newIntervals.word;

import java.util.HashMap;

public class Word8 extends Word {

	private static final HashMap<Long, Word> cache = new HashMap<>();

	public Word8(long val) {
		super(val, 0xFFL);
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
