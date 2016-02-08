/*
 * ExpressionSubstitution.java - This file is part of the Jakstab project.
 * Copyright 2007-2015 Johannes Kinder <jk@jakstab.org>
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, see <http://www.gnu.org/licenses/>.
 */
package org.jakstab.transformation;

import java.util.HashSet;
import java.util.Set;

import org.jakstab.analysis.*;
import org.jakstab.analysis.substitution.ExpressionSubstitutionAnalysis;
import org.jakstab.analysis.substitution.SubstitutionElement;
import org.jakstab.analysis.substitution.SubstitutionState;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.ControlFlowGraph;
import org.jakstab.rtl.Context;
import org.jakstab.rtl.expressions.ExpressionSimplifier;
import org.jakstab.rtl.expressions.RTLExpression;
import org.jakstab.rtl.expressions.RTLVariable;
import org.jakstab.rtl.statements.RTLAssume;
import org.jakstab.rtl.statements.RTLSkip;
import org.jakstab.rtl.statements.RTLStatement;
import org.jakstab.util.Logger;

/**
 * @author Johannes Kinder
 */
public class ExpressionSubstitution implements CFATransformation {

	private static final Logger logger = Logger
			.getLogger(ExpressionSubstitution.class);
	
	private CPAAlgorithm cpaAlgo;
	private Set<CFAEdge> edgeSet;
	
	public static void substituteCFAEdge(CFAEdge edge, SubstitutionState s) {
		RTLStatement stmt = (RTLStatement)edge.getTransformer();
		RTLStatement newStmt = substituteStatement(stmt, s);
		if (newStmt != stmt)
			edge.setTransformer(newStmt);
	}
	
	public static RTLStatement substituteStatement(RTLStatement stmt, SubstitutionState s) {
		Context substCtx = new Context();
		ExpressionSimplifier simplifier = ExpressionSimplifier.getInstance();
		logger.debug("substituting in: " + stmt + " at " + stmt.getLabel() + " state: " + s);
		logger.debug("substitution state: " + s);
		for (RTLVariable v : stmt.getUsedVariables()) {
			SubstitutionElement el = s.getValue(v);
			logger.debug("substitution value: " + v + " isTop? " + el.isTop());
			if (!el.isTop()) {
				substCtx.addAssignment(v, el.getExpression());
			}
		}
		if (!substCtx.getAssignments().isEmpty()) {
			logger.debug("Old stmt: " + stmt);
			logger.debug("Substitution Context: " + substCtx);
			RTLStatement newStmt = stmt.copy().evaluate(substCtx);
			logger.debug("New stmt: " + newStmt);
			//if substitution not empty, try to reduce once more (Empty context)
			if (newStmt != null) {
				RTLStatement reduced = newStmt.evaluate(new Context());
				//if reduction is not empty, return it. Otherwise return skip
				if (reduced != null) {
					if(reduced instanceof RTLAssume) {
						//execute simplification on assumption
						RTLAssume assumption = (RTLAssume) reduced;
						logger.debug("handing assumption of to simplifier: " + assumption);
						RTLExpression newExpr = simplifier.simplify(assumption.getAssumption());
						RTLAssume newAssumption = new RTLAssume(newExpr, assumption.getSource());
						newAssumption.setLabel(assumption.getLabel());
						newAssumption.setNextLabel(assumption.getNextLabel());
						logger.debug("result of simplifier: " + newAssumption);
						return newAssumption;
					}
					return reduced;
				}
			}
			RTLSkip skip = new RTLSkip();
			skip.setLabel(stmt.getLabel());
			skip.setNextLabel(stmt.getNextLabel());
			return skip;
		}
		return stmt;
	}
	
	public ExpressionSubstitution(ControlFlowGraph cfg) {
		cpaAlgo = CPAAlgorithm.createForwardAlgorithm(cfg, new ExpressionSubstitutionAnalysis());
		edgeSet = new HashSet<CFAEdge>(cfg.getEdges());
	}
	
	public Set<CFAEdge> getCFA() {
		return edgeSet;
	}


	@Override
	public void run() {
		
		logger.info("Starting expression substitution.");
		long startTime = System.currentTimeMillis();
		
		cpaAlgo.run();
		ReachedSet exprSubstStates = cpaAlgo.getReachedStates().select(1);
		
		for (CFAEdge edge : edgeSet) {
			assert exprSubstStates.where(edge.getSource()).size() == 1;
			SubstitutionState s = (SubstitutionState)exprSubstStates.where(edge.getSource()).iterator().next();
			substituteCFAEdge(edge, s);
		}
		
		long endTime = System.currentTimeMillis();
		logger.verbose("Finished after " + (endTime - startTime) + "ms.");
	}
	
	public void stop() {
		cpaAlgo.stop();
	}
}
