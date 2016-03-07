package org.jakstab.util;

import java.util.Iterator;

public class IterableIterator<T> implements Iterable<T> {

	private final Iterator<T> iterator;

	public IterableIterator(Iterator<T> iterator) {
		this.iterator = iterator;
	}

	@Override
	public Iterator<T> iterator() {
		return iterator;
	}
}
