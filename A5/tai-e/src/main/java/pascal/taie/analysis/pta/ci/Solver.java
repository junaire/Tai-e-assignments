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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;
import polyglot.ast.Call;

import java.awt.*;
import java.util.Collection;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        if (callGraph.addReachableMethod(method)) {
            for (Stmt stmt : method.getIR().getStmts()) {
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        @Override
        public Void visit(New stmt) {
            workList.addEntry(pointerFlowGraph.getVarPtr(stmt.getLValue()), new PointsToSet(heapModel.getObj(stmt)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getRValue()), pointerFlowGraph.getVarPtr(stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            JMethod m = stmt.getMethodRef().resolve();
            if (stmt.isStatic()) {
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, m))) {
                    addReachable(m);

                    // Parameters.
                    for (int i = 0; i < stmt.getInvokeExp().getArgCount(); ++i) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                    }
                    // Return.
                    Var r = stmt.getResult();
                    if (r != null) {
                        for (Var mret : m.getIR().getReturnVars()) {
                            addPFGEdge(pointerFlowGraph.getVarPtr(mret), pointerFlowGraph.getVarPtr(r));
                        }
                    }
                }
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Var y = stmt.getRValue();
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var y = stmt.getLValue();
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(pointerFlowGraph.getStaticField(field), pointerFlowGraph.getVarPtr(y));
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        if (pointerFlowGraph.addEdge(source, target)) {
            PointsToSet pts = source.getPointsToSet();
            if (!pts.isEmpty()) {
                workList.addEntry(target, pts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        while (!workList.isEmpty()) {
            WorkList.Entry entry = workList.pollEntry();
            PointsToSet pts = entry.pointsToSet(); // pts
            Pointer n = entry.pointer();

            PointsToSet delta = propagate(n, pts);
            if (n instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    // x.f = y;
                    for (StoreField storeField : var.getStoreFields()) {
                        Var y = storeField.getRValue();
                        JField field = storeField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getInstanceField(obj, field));
                    }
                    // y = x.f
                    for (LoadField loadField : var.getLoadFields()) {
                        Var y = loadField.getLValue();
                        JField field = loadField.getFieldRef().resolve();
                        addPFGEdge(pointerFlowGraph.getInstanceField(obj, field), pointerFlowGraph.getVarPtr(y));
                    }
                    // x[i] = y;
                    for (StoreArray storeArray : var.getStoreArrays()) {
                        Var y = storeArray.getRValue();
                        addPFGEdge(pointerFlowGraph.getVarPtr(y), pointerFlowGraph.getArrayIndex(obj));
                    }
                    // y = x[i];
                    for (LoadArray loadArray : var.getLoadArrays()) {
                        Var y = loadArray.getLValue();
                        addPFGEdge(pointerFlowGraph.getArrayIndex(obj), pointerFlowGraph.getVarPtr(y));
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet result = new PointsToSet();
        // pts - pt(n)
        for (Obj o : pointsToSet.objects().filter(obj -> !pointer.getPointsToSet().getObjects().contains(obj)).collect(Collectors.toSet())) {
            result.addObject(o);
        }

        if (!pointsToSet.isEmpty()) {
            for (Obj obj : result.getObjects()) {
                pointer.getPointsToSet().addObject(obj);
            }
            for (Pointer s : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(s, result);
            }
        }
        return result;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var  the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        for (Invoke callSite : var.getInvokes()) {
            JMethod m = resolveCallee(recv, callSite); // Dispatch.
            Pointer mThis = pointerFlowGraph.getVarPtr(m.getIR().getThis());
            workList.addEntry(mThis, new PointsToSet(recv)); // Add <mthis, {oi}> to WL.

            CallKind kind = null;
            if (callSite.isStatic()) {
                kind = CallKind.STATIC;
            } else if (callSite.isVirtual()) {
                kind = CallKind.VIRTUAL;
            } else if (callSite.isDynamic()) {
                kind = CallKind.DYNAMIC;
            } else if (callSite.isInterface()) {
                kind = CallKind.INTERFACE;
            } else if (callSite.isSpecial()) {
                kind = CallKind.SPECIAL;
            }

            if (callGraph.addEdge(new Edge<>(kind, callSite, m))) {
                addReachable(m);

                // Parameters.
                for (int i = 0; i < callSite.getInvokeExp().getArgCount(); ++i) {
                    addPFGEdge(pointerFlowGraph.getVarPtr(callSite.getInvokeExp().getArg(i)), pointerFlowGraph.getVarPtr(m.getIR().getParam(i)));
                }
                // Return.
                Var r = callSite.getResult();
                if (r != null) {
                    for (Var mret : m.getIR().getReturnVars()) {
                        addPFGEdge(pointerFlowGraph.getVarPtr(mret), pointerFlowGraph.getVarPtr(r));
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
