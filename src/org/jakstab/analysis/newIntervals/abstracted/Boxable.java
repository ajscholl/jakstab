package org.jakstab.analysis.newIntervals.abstracted;

public interface Boxable<T extends Boxable<T>> {
	AbstractDomain<T> abstractBox();
}
