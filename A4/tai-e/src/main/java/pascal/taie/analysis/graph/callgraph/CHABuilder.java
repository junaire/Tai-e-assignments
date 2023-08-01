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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;
import soot.util.ArraySet;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallKind getCallKind(Invoke callSite) {
        if (callSite.isVirtual()) {
            return CallKind.VIRTUAL;
        } else if (callSite.isStatic()) {
            return CallKind.STATIC;
        } else if (callSite.isInterface()) {
            return CallKind.INTERFACE;
        } else if (callSite.isSpecial()) {
            return CallKind.SPECIAL;
        } else if (callSite.isDynamic()) {
            return CallKind.DYNAMIC;
        }
        return null;
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);

        Queue<JMethod> worklist = new ArrayDeque<>();
        worklist.add(entry);
        while (!worklist.isEmpty()) {
            JMethod method = worklist.poll();
            if (callGraph.addReachableMethod(method)) {
                for (Invoke callSite : callGraph.getCallSitesIn(method)) {
                    Set<JMethod> targets = resolve(callSite);
                    CallKind kind = getCallKind(callSite);
                    assert kind != null;
                    for (JMethod target : targets) {
                        assert target != null;
                        callGraph.addEdge(new Edge<>(kind, callSite, target));
                        worklist.addAll(targets);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        Set<JMethod> methods = new HashSet<>();
        MethodRef ref = callSite.getMethodRef();
        if (callSite.isStatic()) {
            methods.add(dispatch(ref.getDeclaringClass(), ref.getSubsignature()));
        } else if (callSite.isSpecial()) {
            methods.add(dispatch(ref.getDeclaringClass(), ref.getSubsignature()));
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Subsignature subsignature = ref.getSubsignature();
            JClass jClass = ref.getDeclaringClass();

            JMethod method = null;
            if (!jClass.isAbstract()) {
                method = dispatch(jClass, subsignature);
                if (method != null) {
                    methods.add(method);
                }
            }
            hierarchy.addClass(jClass);
            Set<JClass> children = new ArraySet<>();
            if (jClass.isInterface()) {
                children.addAll(hierarchy.getDirectSubinterfacesOf(jClass));
                children.addAll(hierarchy.getDirectImplementorsOf(jClass));
            } else {
                children.addAll(hierarchy.getDirectSubclassesOf(jClass));
            }
            for (JClass child : children) {
                method = dispatch(child, subsignature);
                if (method != null) {
                    methods.add(method);
                }
            }

        } else {
            assert false;
        }
        return methods;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        if (jclass == null) {
            return null;
        }

        JMethod method = jclass.getDeclaredMethod(subsignature);
        if (method != null) {
            return method;
        }

        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
