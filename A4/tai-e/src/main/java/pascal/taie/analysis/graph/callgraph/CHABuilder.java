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

import java.util.*;

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

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod method = workList.poll();
            if (callGraph.addReachableMethod(method)) {
                method.getIR().forEach(stmt -> {
                    if (stmt instanceof Invoke callSite) {
                        //Get Call Kind
                        CallKind callKind;
                        if (callSite.isStatic()) {
                            callKind = CallKind.STATIC;
                        } else if (callSite.isSpecial()) {
                            callKind = CallKind.SPECIAL;
                        } else if (callSite.isInterface()) {
                            callKind = CallKind.INTERFACE;
                        } else {
                            callKind = CallKind.VIRTUAL;
                        }

                        Set<JMethod> callTargets = resolve(callSite);
                        callTargets.forEach(target -> {
                            callGraph.addEdge(new Edge<>(callKind, callSite, target));
                            workList.add(target);
                        });
                    }
                });
            }

        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        Set<JMethod> T = new HashSet<>();
        MethodRef methodRef = callSite.getMethodRef();

        if (callSite.isStatic()) {
            T.add(methodRef.getDeclaringClass().getDeclaredMethod(methodRef.getSubsignature()));
        }

        if (callSite.isSpecial()) {
            T.add(dispatch(methodRef.getDeclaringClass(), methodRef.getSubsignature()));
        }

        //virtual call
        if(callSite.isInterface() || callSite.isVirtual()) {
            JClass current_class = methodRef.getDeclaringClass();
            Queue<JClass> queue = new LinkedList<>();
            queue.add(current_class);
            while (!queue.isEmpty()) {
                JClass c = queue.poll();
                JMethod method = dispatch(c, methodRef.getSubsignature());
                if (method != null) {
                    T.add(method);
                }
//                queue.addAll(c.getSubClasses());
                if (c.isInterface()) {
                    queue.addAll(hierarchy.getDirectSubinterfacesOf(c));
                    queue.addAll(hierarchy.getDirectImplementorsOf(c));
                }
                else {
                    queue.addAll(hierarchy.getDirectSubclassesOf(c));
                }
            }
        }
        return T;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        //TODO - check if this is correct
        if(jclass == null)
            return null;

        JMethod method = jclass.getDeclaredMethod(subsignature);

        if (method != null && !method.isAbstract())
            return method;

        return dispatch(jclass.getSuperClass(), subsignature);
    }
}
