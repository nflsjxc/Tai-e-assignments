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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.*;
import pascal.taie.language.type.Type;
import pascal.taie.util.collection.Pair;

import java.util.*;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // Done - finish me
    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }
    public boolean isSource(CSCallSite csCallSite, CSMethod csCalleeMethod) {
        Invoke callSite = csCallSite.getCallSite();
        JMethod method = csCalleeMethod.getMethod();
        Type returnType = method.getReturnType();
        Source source = new Source(method, returnType);
        return config.getSources().contains(source);
    }

//    public boolean isSink(CSCallSite csCallSite, CSMethod csCalleeMethod) {
//        JMethod method = csCalleeMethod.getMethod();
//        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
//        for (int i = 0; i < args.size(); i++) {
//            Sink sink = new Sink(method, i);
//            if(config.getSinks().contains(sink)) return true;
//        }
//        return false;
//    }
//
//    public void sink(CSCallSite csCallSite, CSMethod csCalleeMethod) {
//        JMethod method = csCalleeMethod.getMethod();
//        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
//        for (int i = 0; i < args.size(); i++) {
//            Sink sink = new Sink(method, i);
//            if(config.getSinks().contains(sink)) {
//
//            }
//        }
//    }

    public Obj getTaintObj(CSCallSite csCallSite, CSMethod csCalleeMethod) {
        if(!isSource(csCallSite, csCalleeMethod)) {
            return null;
        }
        Invoke callSite = csCallSite.getCallSite();
        JMethod method = csCalleeMethod.getMethod();
        Type returnType = method.getReturnType();
        return manager.makeTaint(callSite, returnType); //t_l^u
    }

    public boolean isBaseToResult(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        if (base == null) return false;
        JMethod method = csCalleeMethod.getMethod();
        Type resultType = method.getReturnType();
        TaintTransfer taintTransfer = new TaintTransfer(method, TaintTransfer.BASE, TaintTransfer.RESULT, resultType);
        Var lvar = csCallSite.getCallSite().getLValue();
        return (config.getTransfers().contains(taintTransfer) && lvar != null);
    }

    public Set<Pair<Var, Obj>> baseToResult(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        if (!isBaseToResult(csCallSite, csCalleeMethod, base)) {
            return new HashSet<>();
        }
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<CSObj> basePts = ptaResult.getPointsToSet(base);
        Set<Pair<Var, Obj>> ret = new HashSet<>();
        JMethod method = csCalleeMethod.getMethod();
        Var lvar = csCallSite.getCallSite().getLValue();
        Type resultType = method.getReturnType();
        basePts.forEach(csObj -> {
            if (manager.isTaint(csObj.getObject())) {
                ret.add(new Pair<>(
                        lvar,
                        manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
            }
        });
        return ret;
    }

    public boolean isArgToBase(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        if (base == null) return false;
        JMethod method = csCalleeMethod.getMethod();
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        Type baseType = base.getType();
        for (int i = 0; i < args.size(); i++) {
            TaintTransfer taintTransfer = new TaintTransfer(method, i, TaintTransfer.BASE, baseType);
            if (config.getTransfers().contains(taintTransfer)) return true;
        }
        return false;
    }

    public Set<Pair<Var, Obj>> argToBase(CSCallSite csCallSite, CSMethod csCalleeMethod, CSVar base) {
        if (!isArgToBase(csCallSite, csCalleeMethod, base)) {
            return new HashSet<>();
        }
        JMethod method = csCalleeMethod.getMethod();
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        Type baseType = base.getType();
        PointerAnalysisResult ptaResult = solver.getResult();
        Set<Pair<Var, Obj>> ret = new HashSet<>();
        for (int i = 0; i < args.size(); i++) {
            TaintTransfer taintTransfer = new TaintTransfer(method, i, TaintTransfer.BASE, baseType);
            if (config.getTransfers().contains(taintTransfer)) {
                Var arg = args.get(i);
                CSVar csArg = csManager.getCSVar(csCallSite.getContext(), arg);
                Set<CSObj> argPts = ptaResult.getPointsToSet(csArg);
                argPts.forEach(csObj -> {
                    if (manager.isTaint(csObj.getObject())) {
                        ret.add(new Pair<>(
                                base.getVar(),
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), baseType)));
                    }
                });
            }
        }
        return ret;
    }

    public boolean isArgToResult(CSCallSite csCallSite, CSMethod csCalleeMethod) {
        JMethod method = csCalleeMethod.getMethod();
        Type resultType = method.getReturnType();
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        for (int i = 0; i < args.size(); i++) {
            TaintTransfer taintTransfer = new TaintTransfer(method, i, TaintTransfer.RESULT, resultType);
            if (config.getTransfers().contains(taintTransfer)) return true;
        }
        return false;
    }

    public Set<Pair<Var, Obj>> argToResult(CSCallSite csCallSite, CSMethod csCalleeMethod) {
        if (!isArgToResult(csCallSite, csCalleeMethod)) {
            return new HashSet<>();
        }
        PointerAnalysisResult ptaResult = solver.getResult();
        JMethod method = csCalleeMethod.getMethod();
        Type resultType = method.getReturnType();
        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
        Var lvar = csCallSite.getCallSite().getLValue();
        Set<Pair<Var, Obj>> ret = new HashSet<>();
        for (int i = 0; i < args.size(); i++) {
            TaintTransfer taintTransfer = new TaintTransfer(method, i, TaintTransfer.RESULT, resultType);
            if (config.getTransfers().contains(taintTransfer)) {
                Var arg = args.get(i);
                CSVar csArg = csManager.getCSVar(csCallSite.getContext(), arg);
                Set<CSObj> argPts = ptaResult.getPointsToSet(csArg);
                argPts.forEach(csObj -> {
                    if (manager.isTaint(csObj.getObject())) {
                        ret.add(new Pair<>(
                                lvar,
                                manager.makeTaint(manager.getSourceCall(csObj.getObject()), resultType)));
                    }
                });
            }
        }
        return ret;
    }

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new HashSet<>();
        PointerAnalysisResult result = solver.getResult();
        // Done - finish me
        // You could query pointer analysis results you need via variable result.
        CallGraph<CSCallSite, CSMethod> callGraph = result.getCSCallGraph();
        callGraph.reachableMethods().forEach(csMethod -> {
            callGraph.getCallersOf(csMethod).forEach( csCallSite -> {
                        JMethod method = csMethod.getMethod();
                        List<Var> args = csCallSite.getCallSite().getInvokeExp().getArgs();
                        for (int i = 0; i < args.size(); i++) {
                            Sink sink = new Sink(method, i);
                            Var arg = args.get(i);
                            if(config.getSinks().contains(sink)) {
                                int finalI = i;
                                result.getPointsToSet(arg).forEach(obj -> {
                                    if(manager.isTaint(obj)) {
                                        taintFlows.add(
                                                new TaintFlow(manager.getSourceCall(obj), csCallSite.getCallSite(), finalI));
                                    }
                                });
                            }
                        }
                    }
            );
        });
        return taintFlows;
    }
}
