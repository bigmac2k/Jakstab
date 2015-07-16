package org.jakstab.analysis.intervalsets;

import java.util.Collection;
import java.util.Iterator;
import java.util.Set;

import org.jakstab.analysis.AbstractDomainElement;
import org.jakstab.analysis.LatticeElement;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.PartitionedMemory;
import org.jakstab.analysis.intervals.IntervalElement;
import org.jakstab.rtl.expressions.RTLNumber;
import org.jakstab.util.FastSet;

public class IntervalSetElement implements AbstractDomainElement, Iterable<IntervalElement>{

	private Set<IntervalElement> intervalSet;
	
	private static final int MAX_CONCRETIZATION_SIZE = 1000;
	private final MemoryRegion region;
	private final int bitWidth;
	
	public IntervalSetElement(RTLNumber number){
		bitWidth = number.getBitWidth();
		intervalSet = new FastSet<IntervalElement>();
		intervalSet.add(new IntervalElement(number));
		region = MemoryRegion.GLOBAL;
	}
	
	public IntervalSetElement(IntervalSetElement intervalSetElement) {
		bitWidth = intervalSetElement.getBitWidth();
		intervalSet = new FastSet<IntervalElement>(intervalSetElement.getIntervalSet());
		region = intervalSetElement.getRegion();
	}

	public IntervalSetElement(IntervalElement intervalElement) {
		bitWidth = intervalElement.getBitWidth();
		intervalSet = new FastSet<IntervalElement>();
		intervalSet.add(intervalElement);
		region = intervalElement.getRegion();
	}

	public IntervalSetElement(int bitWidth, MemoryRegion region) {
		this.bitWidth = bitWidth;
		intervalSet = new FastSet<IntervalElement>();
		this.region = region;
	}

	private Set<IntervalElement> getIntervalSet() {
		return intervalSet;
	}

	@Override
	public Set<RTLNumber> concretize() {
		if (getRegion() != MemoryRegion.GLOBAL || size() > MAX_CONCRETIZATION_SIZE) {
			return RTLNumber.ALL_NUMBERS;
		}
		
		Set<RTLNumber> result = new FastSet<RTLNumber>();
		for(IntervalElement intervalElement: intervalSet){
			result.addAll(intervalElement.concretize());
		}
		
		return result;
	}

	private MemoryRegion getRegion() {
		return region;
	}

	private int size() {
		int result = 0;
		for(IntervalElement intervalElement: intervalSet){
			result += intervalElement.size();
		}
		
		return result;
	}

	@Override
	public boolean hasUniqueConcretization() {
		return size() == 1;
	}

	@Override
	public boolean lessOrEqual(LatticeElement l) {
		if(isBot()) return true;
		IntervalSetElement other = (IntervalSetElement)l;
		boolean lessOrEqualFound = false;
		for(IntervalElement otherElement: other){
			lessOrEqualFound = false;
			for(IntervalElement intervalElement: intervalSet){
				if(intervalElement.lessOrEqual(otherElement)){
					lessOrEqualFound = true;
					break;
				}
			}
			// lessOrEqualFound = lessOrEqual(other) was true for at least one interval in this intervalSet
			if(!lessOrEqualFound) return false;
		}

		return true;
	}
	
	private long getLowestLeft(){
		long lowestLeft = Long.MAX_VALUE;
		for(IntervalElement intervalElement: intervalSet){
			if(intervalElement.getLeft() < lowestLeft) lowestLeft = intervalElement.getLeft();
		}
		
		return lowestLeft;
	}
	
	private long getHighestRight(){
		long highestRight = Long.MIN_VALUE;
		for(IntervalElement intervalElement: intervalSet){
			if(intervalElement.getLeft() > highestRight) highestRight = intervalElement.getLeft();
		}
		
		return highestRight;
	}

	@Override
	public boolean isTop() {
		return intervalSet.size() == 1 && intervalSet.contains(IntervalElement.getTop(bitWidth));
	}

	@Override
	public boolean isBot() {
		return intervalSet.isEmpty();
	}

	@Override
	public Collection<? extends AbstractDomainElement> readStorePowerSet(int bitWidth,
			PartitionedMemory<? extends AbstractDomainElement> store) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public AbstractDomainElement readStore(int bitWidth, PartitionedMemory<? extends AbstractDomainElement> store) {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public <A extends AbstractDomainElement> void writeStore(int bitWidth, PartitionedMemory<A> store, A value) {
		// TODO Auto-generated method stub
		
	}

	@Override
	public AbstractDomainElement plus(AbstractDomainElement op) {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		IntervalSetElement other = (IntervalSetElement) op;
		for(IntervalElement intervalElement: intervalSet){
			for(IntervalElement otherElement: other){
				result.add(intervalElement.plus(otherElement));
			}
		}
		
		result.mergeSetElements();
		return result;
	}

	private void mergeSetElements() {
		Set<IntervalElement> newIntervalSet = new FastSet<IntervalElement>();
		for(IntervalElement intervalElement1: intervalSet){
			for(IntervalElement intervalElement2: intervalSet){
				if(intervalElement1.getStride() == intervalElement2.getStride() &&
						(intervalElement1.getLeft() < intervalElement2.getRight() 
						|| intervalElement1.getRight() > intervalElement2.getLeft())){
					newIntervalSet.add(intervalElement1.join(intervalElement2));
				}
				else{
					newIntervalSet.add(intervalElement1);
					newIntervalSet.add(intervalElement2);
				}
			}
		}
		
		if(newIntervalSet.contains(IntervalElement.getTop(bitWidth))){
			intervalSet = new FastSet<IntervalElement>(IntervalElement.getTop(bitWidth));
		}
		else{			
			intervalSet = newIntervalSet;
		}
	}

	@Override
	public AbstractDomainElement negate() {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		for(IntervalElement intervalElement : intervalSet){
			result.add(intervalElement.negate());
		}
		
		return result;
	}

	private void add(IntervalElement elementToAdd) {
		assert(elementToAdd.getBitWidth() == bitWidth);
		for(IntervalElement intervalElement : intervalSet){
			if(elementToAdd.lessOrEqual(intervalElement)){
				return;
			}
			
			if(elementToAdd.getStride() == intervalElement.getStride()
					&& (elementToAdd.getLeft() >= intervalElement.getRight()
					|| intervalElement.getLeft() >= elementToAdd.getRight())){
				intervalSet.add(intervalElement.join(elementToAdd));
				intervalSet.remove(intervalElement);
				mergeSetElements();
				return;
			}
		}
	}

	@Override
	public AbstractDomainElement multiply(AbstractDomainElement op) {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		IntervalSetElement other = (IntervalSetElement) op;
		for(IntervalElement intervalElement: intervalSet){
			for(IntervalElement otherElement: other){
				result.add(intervalElement.multiply(otherElement));
			}
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement bitExtract(int first, int last) {
		int newBitWidth = last - first + 1;
		IntervalSetElement result = new IntervalSetElement(newBitWidth, region);
		for(IntervalElement intervalElement : intervalSet){
			result.add(intervalElement.bitExtract(first, last));
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement signExtend(int first, int last) {
		int newBitWidth = Math.max(bitWidth, last + 1);
		IntervalSetElement result = new IntervalSetElement(newBitWidth, region);
		for(IntervalElement intervalElement : intervalSet){
			result.add(intervalElement.signExtend(first, last));
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement zeroFill(int first, int last) {
		int newBitWidth = Math.max(bitWidth, last + 1);
		IntervalSetElement result = new IntervalSetElement(newBitWidth, region);
		for(IntervalElement intervalElement : intervalSet){
			result.add(intervalElement.zeroFill(first, last));
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement and(AbstractDomainElement op) {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		IntervalSetElement other = (IntervalSetElement) op;
		for(IntervalElement intervalElement: intervalSet){
			for(IntervalElement otherElement: other){
				result.add(intervalElement.and(otherElement));
			}
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement or(AbstractDomainElement op) {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		IntervalSetElement other = (IntervalSetElement) op;
		for(IntervalElement intervalElement: intervalSet){
			for(IntervalElement otherElement: other){
				result.add(intervalElement.or(otherElement));
			}
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement xOr(AbstractDomainElement op) {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		IntervalSetElement other = (IntervalSetElement) op;
		for(IntervalElement intervalElement: intervalSet){
			for(IntervalElement otherElement: other){
				result.add(intervalElement.xOr(otherElement));
			}
		}
		
		result.mergeSetElements();
		return result;	
	}

	@Override
	public AbstractDomainElement join(LatticeElement l) {
		IntervalSetElement other = (IntervalSetElement) l;
		IntervalSetElement result = new IntervalSetElement(this);
		result.intervalSet.addAll(other.intervalSet);
		result.mergeSetElements();
		return result;
	}

	@Override
	public Iterator<IntervalElement> iterator() {
		return intervalSet.iterator();
	}
	
	@Override
	public String toString(){
		String s = "";
		s += "{";
		int i = intervalSet.size();
		for(IntervalElement intervalElement : intervalSet){
			if(i>0){
				s += intervalElement.toString() + ", ";				
			}
			else{
				s += intervalElement.toString() + "}";				
			}
		}
		
		return s;
	}
	
	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		IntervalSetElement other = (IntervalSetElement) obj;
		for(IntervalElement intervalElement : intervalSet){
			if(!other.intervalSet.contains(intervalElement)){
				return false;
			}
		}
		for(IntervalElement otherIntervalElement : other){
			if(!intervalSet.contains(otherIntervalElement)){
				return false;
			}
		}
		
		return true;
	}
	
	public static IntervalSetElement getTop(int bitWidth){
		IntervalSetElement result = new IntervalSetElement(IntervalElement.getTop(bitWidth));
		return result;
	}

	public int getBitWidth() {
		return bitWidth;
	}

	@Override
	public AbstractDomainElement bitNegate() {
		IntervalSetElement result = new IntervalSetElement(bitWidth, region);
		for(IntervalElement intervalElement: intervalSet){
				result.add(intervalElement.bitNegate());
		}
		
		result.mergeSetElements();
		return result;	
	}

}
