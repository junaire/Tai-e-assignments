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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.stream.Collectors;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    void solve() {
        initialize();
        analyze();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        if (callGraph.addReachableMethod(csMethod)) {
            StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
            stmtProcessor.run();
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        public void run() {
            for (Stmt stmt : csMethod.getMethod().getIR().getStmts()) {
                stmt.accept(this);
            }
        }

        @Override
        public Void visit(New stmt) {
            Obj obj = heapModel.getObj(stmt);
            Context ctx = contextSelector.selectHeapContext(csMethod, obj);

            workList.addEntry(csManager.getCSVar(context, stmt.getLValue()), PointsToSetFactory.make(csManager.getCSObj(ctx, obj)));
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            addPFGEdge(csManager.getCSVar(context, stmt.getRValue()), csManager.getCSVar(context, stmt.getLValue()));
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                Var y = stmt.getRValue();
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(csManager.getCSVar(context, y), csManager.getStaticField(field));
            }
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                Var y = stmt.getLValue();
                JField field = stmt.getFieldRef().resolve();
                addPFGEdge(csManager.getStaticField(field), csManager.getCSVar(context, y));
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                JMethod m = stmt.getMethodRef().resolve();
                CSCallSite csCallSite = csManager.getCSCallSite(context, stmt);
                Context ctx = contextSelector.selectContext(csCallSite, m);

                CSMethod csMethod = csManager.getCSMethod(ctx, m);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csCallSite, csMethod))) {
                    addReachable(csMethod);

                    // Parameters.
                    for (int i = 0; i < stmt.getInvokeExp().getArgCount(); ++i) {
                        addPFGEdge(csManager.getCSVar(context, stmt.getInvokeExp().getArg(i)), csManager.getCSVar(ctx, m.getIR().getParam(i)));
                    }
                    // Return.
                    Var r = stmt.getResult();
                    if (r != null) {
                        for (Var mret : m.getIR().getReturnVars()) {
                            addPFGEdge(csManager.getCSVar(ctx, mret), csManager.getCSVar(context, r));
                        }
                    }
                }
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
            PointsToSet pts = entry.pointsToSet();
            Pointer n = entry.pointer();

            PointsToSet delta = propagate(n, pts);
            if (n instanceof CSVar csVar) {
                for (CSObj csObj : delta) {
                    // x.f = y
                    for (StoreField storeField : csVar.getVar().getStoreFields()) {
                        addPFGEdge(csManager.getCSVar(csVar.getContext(), storeField.getRValue()), csManager.getInstanceField(csObj, storeField.getFieldRef().resolve()));
                    }
                    // y = x.f
                    for (LoadField loadField : csVar.getVar().getLoadFields()) {
                        addPFGEdge(csManager.getInstanceField(csObj, loadField.getFieldRef().resolve()), csManager.getCSVar(csVar.getContext(), loadField.getLValue()));
                    }
                    // x[i] = y;
                    for (StoreArray storeArray : csVar.getVar().getStoreArrays()) {
                        Var y = storeArray.getRValue();
                        addPFGEdge(csManager.getCSVar(csVar.getContext(), y), csManager.getArrayIndex(csObj));
                    }
                    // y = x[i];
                    for (LoadArray loadArray : csVar.getVar().getLoadArrays()) {
                        Var y = loadArray.getLValue();
                        addPFGEdge(csManager.getArrayIndex(csObj), csManager.getCSVar(csVar.getContext(), y));
                    }
                    processCall(csVar, csObj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        PointsToSet result = PointsToSetFactory.make();
        // pts - pt(n)
        for (CSObj o : pointsToSet.objects().filter(obj -> !pointer.getPointsToSet().getObjects().contains(obj)).collect(Collectors.toSet())) {
            result.addObject(o);
        }

        if (!result.isEmpty()) {
            for (CSObj obj : result.getObjects()) {
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        for (Invoke callSite : recv.getVar().getInvokes()) {
            JMethod m = resolveCallee(recvObj, callSite);
            CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), callSite);
            Context ctx = contextSelector.selectContext(csCallSite, recvObj, m);
            CSMethod csMethod = csManager.getCSMethod(ctx, m); // ct:m
            Pointer mThis = csManager.getCSVar(ctx, m.getIR().getThis()); // ct:mthis
            workList.addEntry(mThis, PointsToSetFactory.make(recvObj));

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

            if (callGraph.addEdge(new Edge<>(kind, csCallSite, csMethod))) {
                addReachable(csMethod);

                // Parameters.
                for (int i = 0; i < callSite.getInvokeExp().getArgCount(); ++i) {
                    addPFGEdge(csManager.getCSVar(recv.getContext(), callSite.getInvokeExp().getArg(i)), csManager.getCSVar(ctx, m.getIR().getParam(i)));
                }
                // Return.
                Var r = callSite.getResult();
                if (r != null) {
                    for (Var mret : m.getIR().getReturnVars()) {
                        addPFGEdge(csManager.getCSVar(ctx, mret), csManager.getCSVar(recv.getContext(), r));
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
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
