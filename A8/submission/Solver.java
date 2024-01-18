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

import heros.flowfunc.Transfer;
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
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.util.collection.Pair;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

import java.util.*;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    private Map<CSVar, Set<Invoke>> argToInvokeMap;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
        this.argToInvokeMap = new HashMap<>();
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
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
        // Done - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            IR methodBody = csMethod.getMethod().getIR();
            methodBody.getStmts().forEach(stmt -> {
                stmt.accept(new StmtProcessor(csMethod));
            });
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

        // Done - if you choose to implement addReachable()
        //  via visitor pattern, then finish me

        @Override
        // x = new T();
        public Void visit(New stmt) {
            CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context heapContext = contextSelector.selectHeapContext(csMethod, obj);
            //add {x,o{i}} to workList
            workList.addEntry(varPtr, PointsToSetFactory.make(csManager.getCSObj(heapContext, obj)));
            return null;
        }

        @Override
        // x = y;
        public Void visit(Copy stmt) {
            CSVar lPtr = csManager.getCSVar(context, stmt.getLValue());
            CSVar rPtr = csManager.getCSVar(context, stmt.getRValue());
            // y->x
            addPFGEdge(rPtr, lPtr);
            return null;
        }

        @Override
        // static store T.f = y;
        public Void visit(StoreField stmt) {
            if (stmt.isStatic()) {
                CSVar varPtr = csManager.getCSVar(context, stmt.getRValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticFieldPtr = csManager.getStaticField(field);
                // y->T.f
                addPFGEdge(varPtr, staticFieldPtr);
            }
            return null;
        }

        @Override
        // static load y = T.f;
        public Void visit(LoadField stmt) {
            if (stmt.isStatic()) {
                CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField staticFieldPtr = csManager.getStaticField(field);
                // T.f->y
                addPFGEdge(staticFieldPtr, varPtr);
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
                Context calleeContext = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), method);
                processCallRoutine(csManager.getCSCallSite(context, stmt),
                        csManager.getCSMethod(calleeContext, method), null);
            }

            // Notice: we need to keep track of the arg variables, so that if the argument is tainted, we
            // need to perform processTaint on the related invokes.
            stmt.getInvokeExp().getArgs().forEach(arg -> {
                CSVar csVar = csManager.getCSVar(context, arg);
                Set<Invoke> invokeSet = argToInvokeMap.getOrDefault(csVar, new HashSet<>());
                invokeSet.add(stmt);
                argToInvokeMap.put(csVar, invokeSet);
            });
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // Done - finish me
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
        while (!workList.isEmpty()) {
            WorkList.Entry wlEntry = workList.pollEntry();
            Pointer p = wlEntry.pointer();
            PointsToSet pts = wlEntry.pointsToSet();
            PointsToSet delta = propagate(p, pts);
            // p is a variable pointer
            if (p instanceof CSVar csVarPtr) {
                // x is the variable
                Var x = csVarPtr.getVar();
                // Dispatch context
                Context context = csVarPtr.getContext();
                // pts(x) = {o1, o2, ...}
                // for each CS object o_i
                delta.forEach(obj -> {
                    // o.f = y
                    x.getStoreFields().forEach( stmt -> {
                                CSVar varPtr = csManager.getCSVar(context, stmt.getRValue());
                                JField field = stmt.getFieldRef().resolve();
                                InstanceField instanceField = csManager.getInstanceField(obj, field);
                                addPFGEdge(varPtr, instanceField);
                            }
                    );
                    // y = o.f
                    x.getLoadFields().forEach( stmt -> {
                                CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
                                JField field = stmt.getFieldRef().resolve();
                                InstanceField instanceField = csManager.getInstanceField(obj, field);

                                addPFGEdge(instanceField, varPtr);
                            }
                    );
                    // x[i] = y
                    x.getStoreArrays().forEach( stmt -> {
                                CSVar varPtr = csManager.getCSVar(context, stmt.getRValue());
                                ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                                addPFGEdge(varPtr, arrayIndex);
                            }
                    );
                    // y = x[i]
                    x.getLoadArrays().forEach( stmt-> {
                                CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
                                ArrayIndex arrayIndex = csManager.getArrayIndex(obj);
                                addPFGEdge(arrayIndex, varPtr);
                            }
                    );
                    // r = o.f(a1,...an)
                    processCall(csVarPtr, obj);

                    // If the variable is arg and is tainted,
                    // we need to perform arg-to-base transfer on all related callsites
                    if(taintAnalysis.isTaint(obj.getObject())) {
                        argTaint(context, csVarPtr);
                    }
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
        PointsToSet delta = PointsToSetFactory.make();
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
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // Done - finish me
        Var var = recv.getVar();
        var.getInvokes().forEach( invoke -> {
                    JMethod calleeMethod = resolveCallee(recvObj, invoke);
                    CSCallSite csCallSite = csManager.getCSCallSite(recv.getContext(), invoke);
                    Context calleeContext = contextSelector.selectContext(csCallSite, recvObj, calleeMethod);
                    CSMethod csCalleeMethod = csManager.getCSMethod(calleeContext, calleeMethod);
                    if (calleeMethod.getIR().getThis() != null) //not static, m_this extended
                    {
                        CSVar thisPtr = csManager.getCSVar(calleeContext,calleeMethod.getIR().getThis());
                        workList.addEntry(thisPtr, PointsToSetFactory.make(recvObj));
                    }

                    // expand reachable world
                    CallKind callKind = CallGraphs.getCallKind(invoke);
                    // l->m not in CG before, meaning we haven't expanded this method
                    if (callGraph.addEdge(new Edge<>(callKind, csCallSite, csCalleeMethod))) {
                        processCallRoutine(csCallSite, csCalleeMethod, recv);
                    }
                    // Notice: even if we don't expand call graph, we need to process taint transfer
                    taintProcess(csCallSite, csCalleeMethod, recv);
                }
        );
    }

    private void processCallRoutine(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        taintProcess(csCallSite, csCalleeMethod, base);
        // Notice: when we reach here we have ensured that the method should be in the call graph
        addReachable(csCalleeMethod);
        // Notice: Remember for static call we still need to expand callGraph!
        Invoke invoke = csCallSite.getCallSite();
        CallKind callKind = CallGraphs.getCallKind(invoke);
        callGraph.addEdge(new Edge<>(callKind, csCallSite, csCalleeMethod));

        Context callerContext = csCallSite.getContext();
        Context calleeContext = csCalleeMethod.getContext();
        //parameter passing, arg -> function param
        List<Var> params = csCalleeMethod.getMethod().getIR().getParams();
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        assert (params.size() == args.size());
        for (int i = 0; i < params.size(); i++) {
            CSVar argPtr = csManager.getCSVar(callerContext, args.get(i));
            CSVar paramPtr = csManager.getCSVar(calleeContext, params.get(i));
            addPFGEdge(argPtr, paramPtr);
        }
        // return value, function return -> result
        // Notice: sometimes there is no return value!
        if (csCallSite.getCallSite().getLValue() != null) {
            List<Var> returnVars = csCalleeMethod.getMethod().getIR().getReturnVars();
            CSVar resultPtr = csManager.getCSVar(callerContext, csCallSite.getCallSite().getResult());
            returnVars.forEach(ret -> {
                        CSVar retPtr = csManager.getCSVar(calleeContext, ret);
                        addPFGEdge(retPtr, resultPtr);
                    }
            );

        }
    }

    void argTaint(Context context, CSVar csVar) {
//        System.out.println("+++++++++++Arg tainting+++++++++++++++");
        Set<Invoke> relatedInvokes = argToInvokeMap.getOrDefault(csVar, new HashSet<>());
        getResult();
        relatedInvokes.forEach(invoke -> {
            CSCallSite csCallSite = csManager.getCSCallSite(context, invoke);
            // virtual call
            if (invoke.getInvokeExp() instanceof InvokeInstanceExp) {
                CSVar base =csManager.getCSVar(context, ((InvokeInstanceExp) invoke.getInvokeExp()).getBase());
                // base is recv obj
                result.getPointsToSet(base).forEach(csObj -> {
                    JMethod calleeMethod = resolveCallee(csObj, invoke);
                    Context calleeContext = contextSelector.selectContext(csCallSite, csObj, calleeMethod);
                    CSMethod csCalleeMethod = csManager.getCSMethod(calleeContext, calleeMethod);
                    taintProcess(csCallSite, csCalleeMethod, base);
                });
            }
            // static call
            if (invoke.isStatic()) {
                JMethod method = resolveCallee(null, invoke);
                Context calleeContext = contextSelector.selectContext(csManager.getCSCallSite(context, invoke), method);
                CSMethod csCalleeMethod = csManager.getCSMethod(calleeContext, method);
                taintProcess(csCallSite, csCalleeMethod, null);
            }
        });
    }

    void taintProcess(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        // Done - finish me
        // This function is used to process taint transfer on calls
        // 1. Call(Source)
        if (taintAnalysis.isSource(csCallSite, csCalleeMethod)) {
            Obj taintObj = taintAnalysis.getTaintObj(csCallSite, csCalleeMethod);
            Var lVar = csCallSite.getCallSite().getLValue();
            if (lVar != null) {
                CSVar lVarPtr = csManager.getCSVar(csCallSite.getContext(), lVar);
                CSObj csTaintObj = csManager.getCSObj(contextSelector.getEmptyContext(), taintObj); // []: t_l^u
                workList.addEntry(lVarPtr, PointsToSetFactory.make(csTaintObj));
            }
        }

        // 2. Call(Sink) This part is processed in collectTaintFlows()
//        if (taintAnalysis.isSink(csCallSite, csCalleeMethod)) {
//            taintAnalysis.sink(csCallSite, csCalleeMethod);
//        }

        // 3. Call(base-to-result)
        if (taintAnalysis.isBaseToResult(csCallSite, csCalleeMethod, base)) {
            Set<Pair<Var, Obj>> ret = taintAnalysis.baseToResult(csCallSite, csCalleeMethod, base);
            ret.forEach(pair -> {
                CSVar csVar = csManager.getCSVar(csCallSite.getContext(), pair.first());
                CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), pair.second());
                workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            });
        }

        // 4. Call(arg-to-base)
        if (taintAnalysis.isArgToBase(csCallSite, csCalleeMethod, base)) {
            Set<Pair<Var, Obj>> ret = taintAnalysis.argToBase(csCallSite, csCalleeMethod, base);
            ret.forEach(pair -> {
                CSVar csVar = csManager.getCSVar(csCallSite.getContext(), pair.first());
                CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), pair.second());
                workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            });
        }

        // 5. Call(arg-to-result)
        if (taintAnalysis.isArgToResult(csCallSite, csCalleeMethod)) {
            Set<Pair<Var, Obj>> ret = taintAnalysis.argToResult(csCallSite, csCalleeMethod);
            ret.forEach(pair -> {
                CSVar csVar = csManager.getCSVar(csCallSite.getContext(), pair.first());
                CSObj csObj = csManager.getCSObj(contextSelector.getEmptyContext(), pair.second());
                workList.addEntry(csVar, PointsToSetFactory.make(csObj));
            });
        }



    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
