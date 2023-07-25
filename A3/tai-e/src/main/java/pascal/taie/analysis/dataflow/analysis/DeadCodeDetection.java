/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));

        deadCode.addAll(analyzeControlFlowUnreachable(cfg));
        deadCode.addAll(analyzeBranchesUnreachable(cfg, constants));
        deadCode.addAll(analyzeDeadAssignment(cfg, liveVars));

        // Your task is to recognize dead code in ir and add it to deadCode
        return deadCode;
    }

    private Set<Stmt> analyzeDeadAssignment(CFG<Stmt> cfg, DataflowResult<Stmt, SetFact<Var>> liveVars) {
        Set<Stmt> dead = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg.getNodes()) {
            if (stmt instanceof AssignStmt<?,?> assignStmt) {
                LValue lValue = assignStmt.getLValue();
                RValue rValue = assignStmt.getRValue();

                SetFact<Var> facts = liveVars.getOutFact(stmt);
                if (lValue instanceof Var var) {
                    if (!facts.contains(var) && hasNoSideEffect(rValue)) {
                        dead.add(stmt);
                    }
                }
            }
        }
        return dead;
    }

    private Set<Stmt> analyzeBranchesUnreachable(CFG<Stmt> cfg, DataflowResult<Stmt, CPFact> constants) {
        Set<Stmt> dead = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg.getNodes()) {
            if (stmt instanceof If ifStmt) {
                ConditionExp condition = ifStmt.getCondition();
                CPFact facts = constants.getOutFact(stmt);

                Value v1 = facts.get(condition.getOperand1());
                Value v2 = facts.get(condition.getOperand2());

                if (!v1.isConstant() || !v2.isConstant()) {
                    continue;
                }

                // Which edge is dead?
                Edge.Kind deadEdgeKind;
                if (evaluateCondition(condition, v1, v2)) {
                    deadEdgeKind = Edge.Kind.IF_FALSE;
                } else {
                    deadEdgeKind = Edge.Kind.IF_TRUE;
                }

                Stmt candidate = null;
                List<Edge<Stmt>> edges = new ArrayList<>(cfg.getOutEdgesOf(ifStmt));
                for (Edge<Stmt> edge : edges) {
                    if (edge.getKind() == deadEdgeKind) {
                        candidate = edge.getTarget();
                    }
                }

                dead.addAll(addDeadStmtChain(cfg, candidate));

            } else if (stmt instanceof SwitchStmt switchStmt) {
                CPFact facts = constants.getOutFact(switchStmt);
                Value value = facts.get(switchStmt.getVar());

                if (!value.isConstant()) {
                    continue;
                }

                boolean matched = false;
                for (Pair<Integer, Stmt> cs : switchStmt.getCaseTargets()) {
                    if (cs.first() == value.getConstant()) {
                        matched = true;
                    } else {
                        dead.addAll(addDeadStmtChain(cfg, cs.second()));
                    }
                }
                if (matched) {
                    dead.addAll(addDeadStmtChain(cfg, switchStmt.getDefaultTarget()));
                }
            }
        }
        return dead;
    }

    private boolean evaluateCondition(ConditionExp condition, Value v1, Value v2) {
        return switch (condition.getOperator()) {
            case EQ -> v1.getConstant() == v2.getConstant();
            case NE -> v1.getConstant() != v2.getConstant();
            case LT -> v1.getConstant() < v2.getConstant();
            case GT -> v1.getConstant() > v2.getConstant();
            case LE -> v1.getConstant() <= v2.getConstant();
            case GE -> v1.getConstant() >= v2.getConstant();
        };
    }

    private List<Stmt> addDeadStmtChain(CFG<Stmt> cfg, Stmt candidate) {
        List<Stmt> dead = new ArrayList<>();
        while (cfg.getInEdgesOf(candidate).size() == 1 && !cfg.isExit(candidate)) {
            dead.add(candidate);
            List<Edge<Stmt>> outEdges = new ArrayList<>(cfg.getOutEdgesOf(candidate));
            if (outEdges.size() != 1) {
                break;
            }
            candidate = outEdges.get(0).getTarget();
        }
        return dead;
    }

    private Set<Stmt> analyzeControlFlowUnreachable(CFG<Stmt> cfg) {
        Set<Stmt> dead = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        for (Stmt stmt : cfg.getNodes()) {
            if (!cfg.isEntry(stmt) && cfg.getPredsOf(stmt).isEmpty()) {
                dead.add(stmt);
            }
        }
        return dead;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
