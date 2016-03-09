package org.jakstab.analysis.newIntervals.word;

import java.util.HashMap;

public class Word32 extends Word {

	private static HashMap<Long, Word> cache = new HashMap<>();

	public Word32(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 0xFFFFFFFFL;
	}

	@Override
	public Word mkThis(long val) {
		return new Word32(val);
	}

	@Override
	protected HashMap<Long, Word> getCache() {
		return cache;
	}

	@Override
	public long longValue() {
		int v = (int)val;
		return (long)v;
	}
}
