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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Pair;

import java.util.*;
import java.util.concurrent.atomic.AtomicBoolean;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public static PointerAnalysisResult pta;
    public static Map<Obj, Set<Var>> objToVar = new HashMap<>();
    public static Map<Var, Set<Var>> varAliasMap = new HashMap<>();
    public static Map<Pair<?, FieldRef>, Value> instanceManager = new HashMap<>();
    //This is the map maintaining instance values
    public static Map<Pair<?, Value>, Value> arrayManager = new HashMap<>();
    //This is the map maintaining array values
    public static Map<Pair<JClass, JField>, Value> staticValManager = new HashMap<>();
    //This is the map maintaining static field values
    //K1: JClass, K2: JField, V: Value

    public static Map<Pair<Var, FieldRef>, Value> varManager = new HashMap<>();
    // This is the map maintaining variable values
    public static Map<Pair<JClass, JField>, Set<LoadField>> staticLoadFields = new HashMap<>();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
        cp.interCP = this;
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        pta = World.get().getResult(ptaId);
        // You can do initialization work here

        // We generate inverse map from object to var
        for(Var var : pta.getVars()){
            for(Obj obj : pta.getPointsToSet(var)){
                Set<Var> s = objToVar.getOrDefault(obj, new HashSet<>());
                s.add(var);
                objToVar.put(obj, s);
            }
        }

        // We generate alias map from var to var
        for(Var var_x: pta.getVars()){
            for(Var var_y: pta.getVars()){
                if(var_x == var_y) continue;
                for(Obj obj: pta.getPointsToSet(var_x)) {
                    if(pta.getPointsToSet(var_y).contains(obj)){
                        // 2 variables are considered to be alias if they point to the same object
                        Set<Var> s = varAliasMap.getOrDefault(var_x, new HashSet<>());
                        s.add(var_y);
                        varAliasMap.put(var_x, s);
                    }
                }
            }
        }

        //  Construct cache for static load field access (T.f = x)
        icfg.getNodes().forEach(stmt -> {
            if(stmt instanceof LoadField s && s.getFieldAccess() instanceof StaticFieldAccess access){
                Pair<JClass, JField> qPair =
                        new Pair<>(access.getFieldRef().getDeclaringClass(), access.getFieldRef().resolve());
                Set<LoadField> set = staticLoadFields.getOrDefault(qPair, new HashSet<>());
                set.add(s);
                staticLoadFields.put(qPair, set);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // Done - finish me
        // From call node in to out
        // For call node the newly created value is processed in transferEdge
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach((key, value) -> {
            if (out.update(key,value)) changed.set(true);
        });
        return changed.get();

    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // Done - finish me
        // From non call node in to out
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // Done - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // Done - finish me
        // From call node to next node
        Invoke callSite = (Invoke) edge.getSource();
        Var lValue = callSite.getLValue();
        CPFact outCopy = out.copy();
        if(lValue != null) {
            outCopy.remove(lValue);
        }
        return outCopy;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // Done - finish me
        // From caller to callee
        // pass args to params
        Invoke callSite = (Invoke) edge.getSource();
        CPFact out = new CPFact();
        List<Var> params = edge.getCallee().getIR().getParams();
        for(int i = 0; i < params.size(); i++) {
            out.update(params.get(i), callSiteOut.get(callSite.getRValue().getArg(i)));
        }
        return out;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // Done - finish me
        // From callee to caller
        Invoke callSite = (Invoke) edge.getCallSite();
        CPFact out = new CPFact();
        Var lValue = callSite.getLValue();
        if (lValue != null) {
            edge.getReturnVars().forEach(var -> {
                out.update(lValue, cp.meetValue(out.get(lValue), returnOut.get(var)));
                // Here's the case:
                // if a = True return 2 else return 1
                // result should be NAC
            });
        }
        return out;
    }
}
