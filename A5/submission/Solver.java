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
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

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
        // Done - finish me
        // Basically we construct the PFG that doesn't need object in this method
        if (callGraph.addReachableMethod(method)) {
            IR methodBody = method.getIR();
            methodBody.getStmts().forEach(stmt -> {
                    stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // Done - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        // x = new T();
        public Void visit(New stmt) {
            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            //add {x,o{i}} to worklist
            workList.addEntry(varPtr, new PointsToSet(obj));
            return null;
        }

        @Override
        // x = y;
        public Void visit(Copy stmt) {
            VarPtr lPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
            VarPtr rPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
            // y->x
            addPFGEdge(rPtr, lPtr);
            return null;
        }

        @Override
        // static store T.f = y;
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                VarPtr varptr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticFieldPtr = pointerFlowGraph.getStaticField(field);
                // y->T.f
                addPFGEdge(varptr, staticFieldPtr);
            }
            return null;
        }

        @Override
        // static load y = T.f;
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                VarPtr varptr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticFieldPtr = pointerFlowGraph.getStaticField(field);
                // T.f->y
                addPFGEdge(staticFieldPtr, varptr);
            }
            return null;
        }

        @Override
        // static call y = T.m(x1, ..., xn);
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                //no receiver object, we only need method here
                JMethod method = resolveCallee(null, stmt);
                // Done - finish static call
                processCallRoutine(stmt, method);
            }
            return null;
        }

    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // Done - finish me
        // add edge s->t
        if (pointerFlowGraph.addEdge(source, target))  {
            if (!source.getPointsToSet().isEmpty())
                workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // Done - finish me
        // TODO - addentrymethod
//        callGraph.entryMethods().forEach(this::addReachable);
        while (!workList.isEmpty()) {
            WorkList.Entry wlEntry = workList.pollEntry();
            Pointer p = wlEntry.pointer();
            PointsToSet pts = wlEntry.pointsToSet();
            PointsToSet delta = propagate(p, pts);
            // p is a variable pointer
            if (p instanceof VarPtr varptr) {
                // x is the variable
                Var x = varptr.getVar();
                // pts(x) = {o1, o2, ...}
                // for each object o_i
                delta.forEach(obj -> {
                    // o.f = y
                    x.getStoreFields().forEach( stmt -> {
                            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                            JField field = stmt.getFieldRef().resolve();
                            InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, field);
                            addPFGEdge(varPtr, instanceField);
                            }
                    );
                    // y = o.f
                    x.getLoadFields().forEach( stmt -> {
                            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                            JField field = stmt.getFieldRef().resolve();
                            InstanceField instanceField = pointerFlowGraph.getInstanceField(obj, field);
                            addPFGEdge(instanceField, varPtr);
                            }
                    );
                    // x[i] = y
                    x.getStoreArrays().forEach( stmt -> {
                            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getRValue());
                            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                            addPFGEdge(varPtr, arrayIndex);
                            }
                    );
                    // y = x[i]
                    x.getLoadArrays().forEach( stmt-> {
                            VarPtr varPtr = pointerFlowGraph.getVarPtr(stmt.getLValue());
                            ArrayIndex arrayIndex = pointerFlowGraph.getArrayIndex(obj);
                            addPFGEdge(arrayIndex, varPtr);
                            }
                    );
                    // r = o.f(a1,...an)
                    processCall(x, obj);
                });
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // Done - finish me
        PointsToSet delta = new PointsToSet();
        if (!pointsToSet.isEmpty()) {
            PointsToSet ptn = pointer.getPointsToSet();
            pointsToSet.forEach(obj -> {
                    if (ptn.addObject(obj)) {
                        delta.addObject(obj);
                    }
            });
            pointerFlowGraph.getSuccsOf(pointer).forEach( ptr -> {
                    workList.addEntry(ptr, delta);
                    }
            );
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // Done - finish me
        var.getInvokes().forEach( invoke -> {
                    JMethod calleeMethod = resolveCallee(recv, invoke);
                    if (calleeMethod.getIR().getThis() != null) //not static, m_this extended
                    {
                        VarPtr thisPtr = pointerFlowGraph.getVarPtr(calleeMethod.getIR().getThis());
                        workList.addEntry(thisPtr, new PointsToSet(recv));
                    }

                    // expand reachable world
                    CallKind callKind = CallGraphs.getCallKind(invoke);
                    // l->m not in CG before, meaning we haven't expanded this method
                    if (callGraph.addEdge(new Edge<>(callKind, invoke, calleeMethod))) {
                        processCallRoutine(invoke, calleeMethod);
                    }
                }
        );
    }

    /**
     * Processes call routine. Connect args to params, and return to result.
     *
     * @param invoke       the invoke statement.
     * @param calleeMethod the callee method.
     */
    private void processCallRoutine(Invoke invoke, JMethod calleeMethod) {
        addReachable(calleeMethod);
        //parameter passing, arg -> function param
        List<Var> params = calleeMethod.getIR().getParams();
        List<Var> args = invoke.getInvokeExp().getArgs();
        assert (params.size() == args.size());
        for (int i = 0; i < params.size(); i++) {
            VarPtr paramPtr = pointerFlowGraph.getVarPtr(params.get(i));
            VarPtr argPtr = pointerFlowGraph.getVarPtr(args.get(i));
            addPFGEdge(argPtr, paramPtr);
        }
        // return value, function return -> result
        // Notice: sometimes there is no return value!
        if (invoke.getResult() != null) {
            List<Var> returnVars = calleeMethod.getIR().getReturnVars();
            VarPtr resultPtr = pointerFlowGraph.getVarPtr(invoke.getResult());
            returnVars.forEach(ret -> {

                        VarPtr retPtr = pointerFlowGraph.getVarPtr(ret);
                        addPFGEdge(retPtr, resultPtr);
                    }
            );
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
