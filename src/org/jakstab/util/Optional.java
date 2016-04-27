package org.jakstab.util;

public final class Optional<T> {
	private final T val;

	private static final Optional<?> NONE = new Optional<>();

	public Optional(T val) {
		assert val != null;
		this.val = val;
	}

	private Optional() {
		val = null;
	}

	public boolean hasValue() {
		return val != null;
	}

	public T getValue() {
		assert val != null;
		return val;
	}

	@Override
	public String toString() {
		if(hasValue()) {
			return val.toString();
		} else {
			return "None";
		}
	}

	@Override
	public boolean equals(Object other) {
		if(other instanceof Optional<?>) {
			Optional<?> opt = (Optional<?>) other;
			return hasValue() == opt.hasValue() && (!hasValue() || getValue().equals(opt.getValue()));
		} else {
			return false;
		}
	}

	@Override
	public int hashCode() {
		if(hasValue()) {
			return getValue().hashCode();
		} else {
			return 0;
		}
	}

	@SuppressWarnings("unchecked")
	public static <T> Optional<T> none() {
		return (Optional<T>)NONE;
	}

	public static <T> Optional<T> optional(T val) {
		return val == null ? Optional.<T>none() : new Optional<>(val);
	}
}
