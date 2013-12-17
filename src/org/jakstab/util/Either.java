package org.jakstab.util;

public class Either<L, R> {
	L l;
	R r;
	public Either(L left, R right) {
		assert (left == null || right == null) && (left != null || right != null) : "Supply either left or right";
		this.l = left;
		this.r = right;
	}
	public boolean isLeft() {
		return getLeft() != null;
	}
	public boolean isRight() {
		return getRight() != null;
	}
	public L getLeft() {
		return l;
	}
	public R getRight() {
		return r;
	}
	@Override
	public String toString() {
		if(isLeft())
			return "Left(" + getLeft().toString() + ")";
		else
			return "Right(" + getRight().toString() + ")";
	}
	@Override
	public boolean equals(Object other) {
		if(other instanceof Either<?, ?>) {
			Either<?, ?> either = (Either<?, ?>) other;
			return ((getLeft() == null && either.getLeft() == null) || getLeft().equals(either.getLeft()))
				&& ((getRight() == null && either.getRight() == null) || getRight().equals(either.getLeft()));
		} else
			return false;
	}
	@Override
	public int hashCode() {
		if(isLeft())
			return getLeft().hashCode();
		else
			return getRight().hashCode();
	}
}