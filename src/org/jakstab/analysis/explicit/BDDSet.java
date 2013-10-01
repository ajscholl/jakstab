package org.jakstab.analysis.explicit;

import java.util.Collection;
import java.util.Set;

import org.jakstab.analysis.AbstractDomainElement;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.rtl.BitVectorType;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.rtl.expressions.LongBWToRTLNumberCaster;
import org.jakstab.rtl.expressions.RTLNumberToLongBWCaster;
import org.jakstab.rtl.expressions.RTLNumberIsDynBoundedBits;
import org.jakstab.util.FastSet;

import cc.sven.tlike.*;

/*
 * This is an abstract domain element consisting of a region and a set of RTLNumbers.
 * It is similar to BasedNumberElement of the bounded address tracking domain.
 */
public class BDDSet implements AbstractDomainElement, BitVectorType {

	private IntLikeSet<Long, RTLNumber> set;
	private MemoryRegion region;
	
	public MemoryRegion getRegion() {
		return region;
	}
	public IntLikeSet<Long, RTLNumber> getSet() {
		return set;
	}
	
	public BDDSet(IntLikeSet<Long, RTLNumber> init) {
		this.set = init;
		this.region = MemoryRegion.GLOBAL;
	}
	public BDDSet(IntLikeSet<Long, RTLNumber> initset, MemoryRegion initregion) {
		this.set = initset;
		this.region = initregion;
	}
	public static BDDSet topBW(int bw) {
		IntLikeSet<Long, RTLNumber> topSet = IntLikeSet$.MODULE$.applyJLong(bw, new RTLNumberIsDynBoundedBits(), new RTLNumberToLongBWCaster(), new LongBWToRTLNumberCaster()).invert();
		return new BDDSet(topSet, MemoryRegion.TOP);
	}
	
	@Override
	public Set<RTLNumber> concretize() {
		Set<RTLNumber> outset = new FastSet<RTLNumber>();
		for(RTLNumber i : getSet().java()) {
			outset.add(i);
		}
		return outset;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return getSet().remove(getSet().randomElement()).isEmpty();
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		BDDSet that = (BDDSet) l;
		return getSet().subsetOf(that.getSet());
	}

	@Override
	public boolean isTop() {
		return getRegion() == MemoryRegion.TOP && getSet().isFull();
	}

	@Override
	public boolean isBot() {
		//There does not seem to be a BOT region
		return false;
	}

	@Override
	public Collection<? extends AbstractDomainElement> readStorePowerSet(
			int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		Set<AbstractDomainElement> result = new FastSet<AbstractDomainElement>();
		//XXX limit to only n elements
		for(RTLNumber rtlnum : getSet().java()) {
			BDDSet res = (BDDSet) store.get(getRegion(),rtlnum.longValue(), getSet().bits());
			result.add(res);
		}
		return result;
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		BDDSet result = null;
		//XXX limit to only n elements
		//XXX what if getSet() is empty -> result will be null
		for (RTLNumber rtlnum : getSet().java()) {
			BDDSet res = (BDDSet) store.get(getRegion(), rtlnum.longValue(), getSet().bits());
			if(result == null) {
				//First iteration - start of reduce (fold1)
				result = res;
			} else {
				MemoryRegion nRegion = result.getRegion().join(res.getRegion());
				if(nRegion == MemoryRegion.TOP || result.getBitWidth() != res.getBitWidth()) {
					result = topBW(Math.max(result.getBitWidth(), res.getBitWidth()));
				} else {
					result = new BDDSet(result.getSet().union(res.getSet()), nRegion);
				}
			}
		}
		return result;
	}

	@Override
	public <X extends AbstractDomainElement> void writeStore(int bitWidth,
			PartitionedMemory<X> store, X value) {
		if(getSet().isFull()) {
			store.setTop();
		} else {
			//XXX what if set is empty? -> exception TODO: check!
			RTLNumber rtlnum = getSet().randomElement();
			   //is singleton?
			if(getSet().remove(rtlnum).isEmpty()) {
				//Strong update
				rtlnum.writeStore(getSet().bits(), store, value);
			} else {
				//Weak update
				for(RTLNumber rtlnums : getSet().java()) {
						store.weakUpdate(getRegion(), rtlnums.longValue(), bitWidth, value);
				}
			}
		}
	}

	@Override
	public AbstractDomainElement plus(AbstractDomainElement op) {
		assert op instanceof BDDSet;
		final BDDSet that = (BDDSet) op;
		MemoryRegion nRegion = getRegion().join(that.getRegion());
		if(nRegion == MemoryRegion.TOP || getBitWidth() != that.getBitWidth()) {
			//XXX we could also return TOP, set (region top, this.set + that.set).
			return topBW(Math.max(getBitWidth(), that.getBitWidth()));
		}
		return new BDDSet(this.getSet().plus(that.getSet()), nRegion);
	}

	@Override
	public AbstractDomainElement negate() {
		return new BDDSet(getSet().negate(), getRegion());
	}

	@Override
	public AbstractDomainElement multiply(AbstractDomainElement op) {
		assert false : "Not implemented";
		return null;
	}

	@Override
	public AbstractDomainElement bitExtract(int first, int last) {
		return new BDDSet(getSet().bitExtract(last, first), getRegion());
	}

	@Override
	public AbstractDomainElement signExtend(int first, int last) {
		return new BDDSet(getSet().signExtend(last, first), getRegion());
	}

	@Override
	public AbstractDomainElement zeroFill(int first, int last) {
		return new BDDSet(getSet().zeroFill(last, first), getRegion());
	}

	@Override
	public AbstractDomainElement join(LatticeElement l) {
		assert l instanceof BDDSet;
		BDDSet that = (BDDSet) l;
		MemoryRegion nRegion = getRegion().join(that.getRegion());
		if(nRegion == MemoryRegion.TOP || getBitWidth() != that.getBitWidth()) {
			//XXX we could also return TOP, set (region top, this.set + that.set).
			return topBW(Math.max(getBitWidth(), that.getBitWidth()));
		}
		return new BDDSet(getSet().union(that.getSet()), nRegion);
	}

	@Override
	public int getBitWidth() {
		return getSet().bits();
	}
}
