package org.jakstab.analysis.newIntervals.abstracted;

/**
 * Interface for things which can be boxed into an abstract domain.
 *
 * @author A. J. Scholl
 * @param <T> The thing we can box.
 */
public interface Boxable<T extends Boxable<T>> {
	AbstractDomain<T> abstractBox();
}
