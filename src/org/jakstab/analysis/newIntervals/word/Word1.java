package org.jakstab.analysis.newIntervals.word;

import java.util.HashMap;

public class Word1 extends Word {

	private static HashMap<Long, Word> cache = new HashMap<>();

	public Word1(long val) {
		super(val);
	}

	@Override
	public long getMask() {
		return 1;
	}

	@Override
	public Word mkThis(long val) {
		return new Word1(val);
	}

	@Override
	protected HashMap<Long, Word> getCache() {
		return cache;
	}

	@Override
	public long longValue() {
		return val == 0 ? 0 : -1;
	}
}
