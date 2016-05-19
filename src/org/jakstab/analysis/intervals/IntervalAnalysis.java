/*
 * IntervalAnalysis.java - This file is part of the Jakstab project.
 * Copyright 2007-2012 Johannes Kinder <jk@jakstab.org>
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
package org.jakstab.analysis.intervals;

import org.jakstab.AnalysisProperties;
import org.jakstab.Program;
import org.jakstab.analysis.*;
import org.jakstab.analysis.explicit.BasedNumberElement;
import org.jakstab.analysis.explicit.BasedNumberValuation;
import org.jakstab.cfa.CFAEdge;
import org.jakstab.cfa.Location;
import org.jakstab.cfa.StateTransformer;
import org.jakstab.rtl.expressions.*;
import org.jakstab.rtl.statements.*;
import org.jakstab.util.Logger;
import org.jakstab.util.MapMap.EntryIterator;
import org.jakstab.util.Pair;

import java.util.Collections;
import java.util.Iterator;
import java.util.Map;
import java.util.Set;

/**
 * A reduced interval congruence analysis with regioned memory. Inspired by
 * Codesurfer's VSA domain.
 *
 * @author Johannes Kinder
 */
public class IntervalAnalysis implements ConfigurableProgramAnalysis {

	public static void register(AnalysisProperties p) {
		p.setShortHand('i');
		p.setName("Interval analysis");
		p.setDescription("Compute strided intervals with region information.");
		p.setExplicit(true);
	}

	@SuppressWarnings("unused")
	private static final Logger logger = Logger.getLogger(IntervalAnalysis.class);
	private AbstractValueFactory<IntervalElement> valueFactory;

	public IntervalAnalysis() {
		valueFactory = new IntervalElementFactory();
	}

	@Override
	public Precision initPrecision(Location location, StateTransformer transformer) {
		return new IntervalPrecision();
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#initStartState(org.jakstab.cfa.Location)
	 */
	@Override
	public AbstractState initStartState(Location label) {
		//IntervalState init = new IntervalState();
		/*init.setValue(Program.getProgram().getArchitecture().stackPointer(),
				new IntervalElement(MemoryRegion.STACK, 0, 0, 0, 32));*/
		//return init;
		return new ValuationState(valueFactory);
	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#merge(org.jakstab.analysis.AbstractState, org.jakstab.analysis.AbstractState)
	 */
	@Override
	public AbstractState merge(AbstractState s1, AbstractState s2, Precision precision) {

		// Widen s2 towards s1.
		//return ((IntervalState)s2).widen((IntervalState)s1);

		if (s2.isTop() || s1.isBot()) return s2;
		if (s1.isTop()) return s1;

		ValuationState current = (ValuationState)s2;
		ValuationState towards = (ValuationState)s1;

		ValuationState widenedState = new ValuationState(valueFactory);
		// Widen variable valuations
		for (Iterator<Map.Entry<RTLVariable,AbstractDomainElement>> entryIt = current.variableIterator(); entryIt.hasNext();) {
			Map.Entry<RTLVariable,AbstractDomainElement> entry = entryIt.next();
			RTLVariable var = entry.getKey();
			IntervalElement v = (IntervalElement)entry.getValue();
			widenedState.setVariableValue(var, v.widen((IntervalElement)towards.getVariableValue(var)));
		}

		// Widen memory
		for (EntryIterator<MemoryRegion, Long, AbstractDomainElement> entryIt = current.storeIterator(); entryIt.hasEntry(); entryIt.next()) {
			MemoryRegion region = entryIt.getLeftKey();
			Long offset = entryIt.getRightKey();
			IntervalElement v = (IntervalElement)entryIt.getValue();
			int bitWidth = v.getBitWidth();
			widenedState.setMemoryValue(region, offset, bitWidth,
					v.widen((IntervalElement)towards.getMemoryValue(region, offset, bitWidth)));
		}

		return widenedState;

	}

	/*
	 * @see org.jakstab.analysis.ConfigurableProgramAnalysis#post(org.jakstab.analysis.AbstractState, org.jakstab.analysis.StateTransformer, org.jakstab.analysis.Precision)
	 */
	@Override
	public Set<AbstractState> post(final AbstractState state, CFAEdge cfaEdge, Precision precision) {

		final RTLStatement statement = (RTLStatement)cfaEdge.getTransformer();
		final ValuationState iState = (ValuationState)state;

		return Collections.singleton(statement.accept(new DefaultStatementVisitor<AbstractState>() {

			@Override
			protected AbstractState visitDefault(RTLStatement stmt) {
				if (!(stmt instanceof RTLSkip)) {
					assert /*!Options.failFast.getValue()*/ false : "no visitor case found for statement: " + stmt;
				}
				return state;
			}

			@Override
			public AbstractState visit(RTLVariableAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				post.setVariableValue((RTLVariable)lhs, evaledRhs);
				return post;
			}

			@Override
			public AbstractState visit(RTLMemoryAssignment stmt) {
				ValuationState post = new ValuationState(iState);
				RTLMemoryLocation m = stmt.getLeftHandSide();
				RTLExpression rhs = stmt.getRightHandSide();
				AbstractDomainElement evaledRhs = iState.abstractEval(rhs);
				AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
				post.setMemoryValue(evaledAddress, m.getBitWidth(), evaledRhs);
				return post;
			}

			private Boolean restrictable(RTLExpression op) {
				if(op instanceof RTLVariable)
					return true;
				if(op instanceof RTLMemoryLocation)
					return true;
				return false;
			}
			private MemoryRegion approxlbregion(MemoryRegion a, MemoryRegion b) {
				if(a.isTop() || b.isBot()) return b;
				if(b.isTop() || a.isBot()) return a;
				//should be top is mo real meet
				if(!a.equals(b)) return MemoryRegion.TOP;
				return a;
			}
			private void restrict(ValuationState post, RTLExpression exp, IntervalElement expvalue, IntervalElement by) {
				MemoryRegion newRegion = approxlbregion(expvalue.getRegion(), by.getRegion());
				if(!newRegion.isTop() && expvalue.getBitWidth() == by.getBitWidth()) {
					IntervalElement newvalue = expvalue.meet(by);
					if (exp instanceof RTLVariable) {
						RTLVariable v = (RTLVariable) exp;
						logger.info("restricting variable " + v + " with contents " + expvalue + " to " + newvalue);
						post.setVariableValue(v, newvalue);
					} else if (exp instanceof RTLMemoryLocation) {
						RTLMemoryLocation m = (RTLMemoryLocation) exp;
						AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
						logger.info("restricting memoryLocation[" + evaledAddress + "] with contents " + expvalue + " to " + newvalue);
						post.setMemoryValue(evaledAddress, m.getBitWidth(), newvalue);
					} else
						logger.info("skipping restriction of " + exp);
				} else
					logger.info("skipping restriction - top region or bitwidth: " + expvalue.getRegion() + " U " + by.getRegion() + " != T && " + expvalue.getBitWidth() + " == " + by.getBitWidth());
			}

			private AbstractState restrictAssume(ValuationState post, RTLExpression assumption, Boolean negated) {
				if(assumption instanceof RTLOperation) {
					RTLOperation op = (RTLOperation) assumption;
					switch (op.getOperator()) {
						case NOT:
							logger.info("found assumption with !");
							return restrictAssume(post, op.getOperands()[0], !negated);
						case EQUAL:
							logger.info("found assumption with ==");
							if (restrictable(op.getOperands()[0]) || restrictable(op.getOperands()[1])) {
								IntervalElement evaledL = (IntervalElement) iState.abstractEval(op.getOperands()[0]);
								IntervalElement evaledR = (IntervalElement) iState.abstractEval(op.getOperands()[1]);
								if (!negated || evaledL.hasUniqueConcretization())
									restrict(post, op.getOperands()[1], evaledR, evaledL);
								if (!negated || evaledR.hasUniqueConcretization())
									restrict(post, op.getOperands()[0], evaledL, evaledR);
								return post;
							}
							break;
						case LESS_OR_EQUAL:
							logger.info("found assumption with <=");
							if (restrictable(op.getOperands()[0]) || restrictable(op.getOperands()[1])) {
								IntervalElement evaledL = (IntervalElement) iState.abstractEval(op.getOperands()[0]);
								IntervalElement evaledR = (IntervalElement) iState.abstractEval(op.getOperands()[1]);
								if (negated) {
									if (evaledL.getRight() != IntervalElement.minBW(evaledL.getBitWidth())) {
										IntervalElement rightRestriction = new IntervalElement(evaledL.getRegion(), evaledL.getRight() - 1, evaledL.getRight() - 1, 1, evaledL.getBitWidth()).openLeft();
										restrict(post, op.getOperands()[1], evaledR, rightRestriction);
									} //else set variable/memory to bot?
									if (evaledR.getLeft() != IntervalElement.maxBW(evaledR.getBitWidth())) {
										IntervalElement leftRestriction = new IntervalElement(evaledR.getRegion(), evaledR.getLeft() + 1, evaledR.getLeft() + 1, 1, evaledR.getBitWidth()).openRight();
										restrict(post, op.getOperands()[0], evaledL, leftRestriction);
									} //else set variable/memory to bot?
								} else {
									restrict(post, op.getOperands()[0], evaledL, evaledR.openLeft());
									restrict(post, op.getOperands()[1], evaledR, evaledL.openRight());
								}
								return post;
							}
							break;
						case LESS: {
							logger.info("found assumption with <");
							RTLExpression rewrite = ExpressionFactory.createNot(ExpressionFactory.createLessOrEqual(op.getOperands()[1], op.getOperands()[0]));
							return restrictAssume(post, rewrite, negated);
						}
						case UNSIGNED_LESS_OR_EQUAL: {
							logger.info("found assumption with u<=");
							IntervalElement evaledL = (IntervalElement) iState.abstractEval(op.getOperands()[0]);
							IntervalElement evaledR = (IntervalElement) iState.abstractEval(op.getOperands()[1]);
							//XXX scm TODO check this - it most certainly is a bug in the ssl generator
							//if (evaledL.getLeft() >= 0 && evaledL.getRight() >= 0 && evaledR.getLeft() >= 0 && evaledR.getRight() >= 0) {
								RTLExpression rewrite = ExpressionFactory.createLessOrEqual(op.getOperands()[0], op.getOperands()[1]);
								return restrictAssume(post, rewrite, negated);
							//}
							//break;
						}
						case UNSIGNED_LESS: {
							logger.info("found assumption with u<");
							IntervalElement evaledL = (IntervalElement) iState.abstractEval(op.getOperands()[0]);
							IntervalElement evaledR = (IntervalElement) iState.abstractEval(op.getOperands()[1]);
							//XXX scm TODO check this - it most certainly is a bug in the ssl generator
							//if (evaledL.getLeft() >= 0 && evaledL.getRight() >= 0 && evaledR.getLeft() >= 0 && evaledR.getRight() >= 0) {
								RTLExpression rewrite = ExpressionFactory.createLessThan(op.getOperands()[0], op.getOperands()[1]);
								return restrictAssume(post, rewrite, negated);
							//}
							//break;
                        }
					}
				}
				logger.info("no case for assumption: " + assumption);
				return post;
			}

			@Override
			public AbstractState visit(RTLAssume stmt) {

				ValuationState post = new ValuationState(iState);

				RTLExpression assumption = stmt.getAssumption();
				return restrictAssume(post, assumption, false);
			}

			@Override
			public AbstractState visit(RTLAlloc stmt) {
				ValuationState post = new ValuationState(iState);
				Writable lhs = stmt.getPointer();

				MemoryRegion newRegion;
				if (stmt.getAllocationName() != null) {
					newRegion = MemoryRegion.create(stmt.getAllocationName());
				} else {
					// TODO: Detect whether this allocation is unique to allow strong updates
					newRegion = MemoryRegion.createAsSummary("alloc" + stmt.getLabel());
				}

				IntervalElement basePointer = new IntervalElement(newRegion,
						ExpressionFactory.createNumber(0, 32));

				if (lhs instanceof RTLVariable) {
					post.setVariableValue((RTLVariable)lhs, basePointer);
				} else {
					RTLMemoryLocation m = (RTLMemoryLocation)lhs;
					AbstractDomainElement evaledAddress = iState.abstractEval(m.getAddress());
					post.setMemoryValue(evaledAddress, m.getBitWidth(), basePointer);
				}

				return post;
			}

			@Override
			public AbstractState visit(RTLHavoc stmt) {
				ValuationState post = new ValuationState(iState);

				// Only create a single state with the havoc range, since this analysis
				// is not path sensitive
				post.setVariableValue(stmt.getVariable(),
						//new IntervalElement(ExpressionFactory.getInstance().createNumber(0, stmt.getVariable().getBitWidth()),
								//(RTLNumber)stmt.getMaximum()));
						new IntervalElement(MemoryRegion.GLOBAL, 0, ((RTLNumber)stmt.getMaximum()).longValue(), 1,
								stmt.getVariable().getBitWidth())
						);

				return post;
			}

			@Override
			public AbstractState visit(RTLUnknownProcedureCall stmt) {
				ValuationState post = new ValuationState(iState);
				for (RTLVariable var : stmt.getDefinedVariables()) {
					post.setVariableValue(var, IntervalElement.getTop(var.getBitWidth()));
				}
				post.setMemoryValue(IntervalElement.getTop(Program.getProgram().getArchitecture().getAddressBitWidth()),
						32, IntervalElement.getTop(32));
				return post;
			}

		}));
	}

	@Override
	public AbstractState strengthen(AbstractState s, Iterable<AbstractState> otherStates,
			CFAEdge cfaEdge, Precision precision) {

		ValuationState state = (ValuationState)s;
		ValuationState strengthenedState = null;

		for (AbstractState t : otherStates) {
			// TODO: Does not work correctly if BoundedAddressTracking returns more than
			// 		 one successor state.
			if (t instanceof BasedNumberValuation) {
				BasedNumberValuation exState = (BasedNumberValuation)t;
				for (Map.Entry<RTLVariable, BasedNumberElement> entry :
					exState.getVariableValuation()) {
					RTLVariable var = entry.getKey();
					BasedNumberElement exVal = entry.getValue();
					if (exVal.isTop() || exVal.isNumberTop())
						continue;
					if (state.getVariableValue(var).isTop()) {
						if (strengthenedState == null) {
							strengthenedState = new ValuationState(state);
						}
						strengthenedState.setVariableValue(var,
								new IntervalElement(exVal.getRegion(),
								exVal.getNumber()));
						//logger.debug("Strengthened state " + state.getIdentifier() +
						//		" by setting " + var + " to " + state.getValue(var));
					}
				}
			}
		}

		return strengthenedState == null ? state : strengthenedState;
	}

	@Override
	public Pair<AbstractState, Precision> prec(AbstractState s,
			Precision precision, ReachedSet reached) {
		return Pair.create(s, precision);
	}

	@Override
	public boolean stop(AbstractState s, ReachedSet reached, Precision precision) {
		return CPAOperators.stopJoin(s, reached, precision);
	}


	private RTLExpression addClause(RTLExpression formula, RTLExpression clause) {
		if (formula != null) {
			return ExpressionFactory.createAnd(formula, clause);
		} else {
			return clause;
		}
	}

	public RTLExpression getStateFormula(ValuationState state) {
		RTLExpression result = null;

		for (Iterator<Map.Entry<RTLVariable,AbstractDomainElement>> entryIt = state.variableIterator(); entryIt.hasNext();) {
			Map.Entry<RTLVariable,AbstractDomainElement> entry = entryIt.next();
			RTLVariable var = entry.getKey();
			IntervalElement interval = (IntervalElement)entry.getValue();

			if (interval.size() == 1) {
				result = addClause(result, ExpressionFactory.createEqual(
						var, ExpressionFactory.createNumber(interval.getLeft(), var.getBitWidth())));
			} else {
				if (!interval.leftOpen()) {
					result = addClause(result, ExpressionFactory.createLessOrEqual(
							ExpressionFactory.createNumber(interval.getLeft(), var.getBitWidth()), var));
				}

				if (!interval.rightOpen()) {
					result = addClause(result, ExpressionFactory.createLessOrEqual(
							var, ExpressionFactory.createNumber(interval.getRight(), var.getBitWidth())));
				}
			}
		}

		if (result == null) {
			result = ExpressionFactory.TRUE;
		}

		return result;
	}

}
