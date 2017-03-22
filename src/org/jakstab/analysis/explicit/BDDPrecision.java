package org.jakstab.analysis.explicit;

import cc.sven.bdd.CBDD;
import cc.sven.bdd.False$;
import org.jakstab.analysis.MemoryRegion;
import org.jakstab.analysis.Precision;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.util.Logger;
import org.jakstab.util.Pair;

import java.util.Map;
import java.util.HashMap;

public class BDDPrecision implements Precision {
	private int count;
	private int rep;

	private Map<RTLVariable, Pair<Integer, Integer>> widenVarTable; // TODO make final, replace get/set with funct
	private Map<Pair<MemoryRegion, Long>, Integer> widenMemTable;
	private final Map<RTLVariable, CBDD> widenVarPrecisionTreeTable;
	private final Map<Pair<MemoryRegion, Long>, CBDD> widenMemPrecisionTreeTable;

	private static final Logger logger = Logger.getLogger(BDDPrecision.class);

	public BDDPrecision() {
		this.count = 0;
		this.rep = 0;
		this.widenVarTable = new HashMap<RTLVariable, Pair<Integer, Integer>>();
		this.widenMemTable = new HashMap<Pair<MemoryRegion, Long>, Integer>();
		this.widenVarPrecisionTreeTable = new HashMap<RTLVariable, CBDD>();
		this.widenMemPrecisionTreeTable = new HashMap<Pair<MemoryRegion, Long>, CBDD>();
	}

	public BDDPrecision(int c, int r, Map<RTLVariable, Pair<Integer, Integer>> widenVarTable, Map<Pair<MemoryRegion,
			Long>, Integer> widenMemTable, Map<RTLVariable, CBDD> widenVarPrecisionTreeTable, Map<Pair<MemoryRegion, Long>, CBDD> widenMemPrecisionTreeTable) {
		this.count = c;
		this.rep = r;
		this.widenVarTable = widenVarTable;
		this.widenMemTable = widenMemTable;
		this.widenVarPrecisionTreeTable = widenVarPrecisionTreeTable;
		this.widenMemPrecisionTreeTable = widenMemPrecisionTreeTable;
	}
	public BDDPrecision copy() {
		return new BDDPrecision(count, rep, widenVarTable, widenMemTable, widenVarPrecisionTreeTable, widenMemPrecisionTreeTable);
	}
	public BDDPrecision incCount() {
		return new BDDPrecision(count + 1, rep, widenVarTable, widenMemTable, widenVarPrecisionTreeTable, widenMemPrecisionTreeTable);
	}
	public int getCount() {
		return count;
	}

	public BDDSet widenVar(RTLVariable key, BDDSet value, BDDSet otherValue){
		if(!widenVarPrecisionTreeTable.containsKey(key)) {
			widenVarPrecisionTreeTable.put(key, False$.MODULE$);
		}
		CBDD widenVarPrecisionTree = widenVarPrecisionTreeTable.get(key);
		logger.info(" ~ var precisionTree before update: " + widenVarPrecisionTree);
		widenVarPrecisionTree = widenVarPrecisionTree.updatePrecisionTree(value.getSet().set().cbdd(),
				otherValue.getSet().set().cbdd());
		widenVarPrecisionTreeTable.put(key, widenVarPrecisionTree);
		logger.info(" ~ var precisionTree after update: " + widenVarPrecisionTree);
		BDDSet widenedVarEntry = new BDDSet(value.getSet().widenPrecisionTree(otherValue.getSet(),
				widenVarPrecisionTree), value.getRegion());
		logger.info(" ~ variable widen result: " + widenedVarEntry);
		return widenedVarEntry;
	}

	public BDDSet widenMem(Pair<MemoryRegion, Long> key, BDDSet value, BDDSet otherValue) {
		if(!widenMemPrecisionTreeTable.containsKey(key)) {
			widenMemPrecisionTreeTable.put(key, False$.MODULE$);
		}
		CBDD widenMemPrecisionTree = widenMemPrecisionTreeTable.get(key);
		logger.info(" ~ mem precisionTree before update: " + widenMemPrecisionTree);
		widenMemPrecisionTree = widenMemPrecisionTree.updatePrecisionTree(value.getSet().set().cbdd(),
				otherValue.getSet().set().cbdd());
		widenMemPrecisionTreeTable.put(key, widenMemPrecisionTree);
		logger.info(" ~ mem precisionTree after update: " + widenMemPrecisionTree);
		BDDSet widenedMemEntry = new BDDSet(value.getSet().widenPrecisionTree(otherValue.getSet(),
				widenMemPrecisionTree), value.getRegion());
		logger.info(" ~ memory widen result: " + widenedMemEntry);
		return widenedMemEntry;
	}
	/* TODO RM
	public Map<RTLVariable, Pair<Integer, Integer>> getWidenVarTable() {
		return widenVarTable;
	}

	public void setWidenVarTable(Map<RTLVariable, Pair<Integer, Integer>> t) {
		this.widenVarTable = t;
	}

	public Map<Pair<MemoryRegion, Long>, Integer> getWidenMemTable() {
		return widenMemTable;
	}

	public void setWidenMemTable(Map<Pair<MemoryRegion, Long>, Integer> t) {
		this.widenMemTable = t;
	}

	public Map<RTLVariable, CBDD> getWidenVarPrecisionTreeTable() {
		return widenVarPrecisionTreeTable;
	}

	public void setWidenVarPrecisionTreeTable(Map<RTLVariable, CBDD> t) {
		this.widenVarPrecisionTreeTable = t;
	}

	public Map<Pair<MemoryRegion, Long>, CBDD> getWidenMemPrecisionTreeTable() {
		return widenMemPrecisionTreeTable;
	}

	public void setWidenMemPrecisionTreeTable(Map<Pair<MemoryRegion, Long>, CBDD> t) {
		this.widenMemPrecisionTreeTable = t;
	}
	*/


	/*
	public BDDPrecision incRep() {
		logger.info(" + incr. rep");
		return new BDDPrecision(count, rep + 1, widenVarTable, widenMemTable, widenVarPrecisionTreeTable, widenMemPrecisionTreeTable);
	}
	public int getRep(){
		return rep;
	}
	*/
	@Override
	public String toString() {
		return "Count: " + ((Integer) count).toString() + ", rep: " + ((Integer) rep).toString();
	}
}
