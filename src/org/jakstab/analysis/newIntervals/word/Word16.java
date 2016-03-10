package org.jakstab.analysis.newIntervals.word;

import java.util.HashMap;

public class Word16 extends Word {

	private static final HashMap<Long, Word> cache = new HashMap<>();

	public Word16(long val) {
		super(val, 0xFFFFL);
	}

	@Override
	public Word mkThis(long val) {
		return new Word16(val);
	}

	@Override
	protected HashMap<Long, Word> getCache() {
		return cache;
	}

	@Override
	public long longValue() {
		short v = (short)val;
		return (long)v;
	}
}
