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

import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.ICFG;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.StaticFieldAccess;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JField;
import pascal.taie.util.collection.Pair;
import pascal.taie.util.collection.SetQueue;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.ir.exp.Var;
import static pascal.taie.analysis.dataflow.inter.InterConstantPropagation.*;
import static pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation.*;


/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // Done - finish me
        for(Node node : icfg) {
            result.setOutFact(node, analysis.newInitialFact());
        }
        icfg.entryMethods().forEach(method -> {
            result.setOutFact(icfg.getEntryOf(method), analysis.newBoundaryFact(icfg.getEntryOf(method)));
        });
    }

    private void doSolve() {
        // Done - finish me
        workList = new LinkedList<>(icfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.poll();
//            System.out.println("Processing node: " + node);
            CPFact in = new CPFact();
            CPFact out = (CPFact) result.getOutFact(node);
            for(ICFGEdge<Node> edge : icfg.getInEdgesOf(node)) {
                analysis.meetInto(analysis.transferEdge(edge, result.getOutFact(edge.getSource())), (Fact) in);
            }

            // We process store here and process load in ConstantPropagation.evaluate
            // Process here to update alias map
            processStoreField((Stmt) node, in);
            processStoreArray((Stmt) node, in);

            if(analysis.transferNode(node, (Fact)in, (Fact)out)) {
                workList.addAll(icfg.getSuccsOf(node));
            }

            result.setInFact(node, (Fact)in);
            result.setOutFact(node, (Fact)out);
        }
    }
    void processStoreField(Stmt stmt, CPFact in) {
        if (stmt instanceof StoreField s) {
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            // Instance store Field: x.f = y
            if(s.getFieldAccess() instanceof InstanceFieldAccess instanceExp) {
//                 ========Version 1: Use instanceManager ===================
                Var base = instanceExp.getBase();
                pta.getPointsToSet(base).forEach( obj ->
                        {
                            Pair<?,FieldRef> qPair = new Pair<>(obj, s.getFieldRef());
                            Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                            Value oldVal = instanceManager.getOrDefault(qPair, Value.getUndef());
                            newVal = meetValue(newVal, oldVal);
                            instanceManager.put(qPair, newVal);
                            if(!newVal.equals(oldVal)) {
                                Set<Var> aliasVars = varAliasMap.getOrDefault(base, new HashSet<>());
                                aliasVars.forEach(var -> {
                                    var.getLoadFields().stream()
                                            .filter(loadField -> loadField.getFieldRef().equals(s.getFieldRef()))
                                            // Only add alias variable load statements where we are operating on the same field to the worklist
                                            .forEach(loadField -> {workList.add((Node) loadField);});
                                });
                            }
                        }
                );
            }
                // ========Version 2: Use varManager(Won't work) ===================
//                Var base = instanceExp.getBase();
//                Pair<String, FieldRef> qPair_var = new Pair<>(base.getName(), s.getFieldRef());
//                Value newVal_var = ConstantPropagation.evaluate(s.getRValue(), in);
//                Value oldVal_var = varManager.getOrDefault(qPair_var, Value.getUndef());
//                newVal_var = meetValue(newVal_var, oldVal_var);
//                varManager.put(qPair_var, newVal_var);
//                if (!newVal_var.equals(oldVal_var)) {
//                    Set<Var> aliasVars = varAliasMap.getOrDefault(base, new HashSet<>());
//                    aliasVars.forEach(var -> {
//                        var.getLoadFields().stream()
//                                .filter(loadField -> loadField.getFieldRef().equals(s.getFieldRef()))
//                                // Only add alias variable load statements where we are operating on the same field to the worklist
//                                .forEach(loadField -> {
//                                    workList.add((Node) loadField);
//                                });
//                    });
//                }
//            }

            // Static field Store: T.f = x
            if(s.getFieldAccess() instanceof StaticFieldAccess staticExp) {
                JClass jClass = staticExp.getFieldRef().getDeclaringClass();
                Pair<JClass, JField> qPair = new Pair<>(jClass, staticExp.getFieldRef().resolve());
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                Value oldVal = staticValManager.getOrDefault(qPair, Value.getUndef());
                newVal = meetValue(newVal, oldVal);
                staticValManager.put(qPair, newVal);
                if(!newVal.equals(oldVal)) {
                    staticLoadFields.getOrDefault(qPair, new HashSet<>()).forEach(loadField -> {
                        workList.add((Node) loadField);
                    });
                }
            }
        }
    }

    void processStoreArray(Stmt stmt, CPFact in) {
        if(stmt instanceof StoreArray s) {
            if(!ConstantPropagation.canHoldInt(s.getRValue())) return;
            ArrayAccess arrayAccess = s.getArrayAccess();
            Value idx = ConstantPropagation.evaluate(arrayAccess.getIndex(), in);
            if (idx.isUndef()) return ;
            Var base = arrayAccess.getBase();
            pta.getPointsToSet(base).forEach(obj -> {
                Pair<?,Value> qPair = new Pair<>(obj, idx);
                Value newVal = ConstantPropagation.evaluate(s.getRValue(), in);
                Value oldVal = arrayManager.getOrDefault(qPair, Value.getUndef());
                newVal = meetValue(newVal, oldVal);
                arrayManager.put(qPair, newVal);
                if(!newVal.equals(oldVal)) {
                    Set<Var> aliasVars = varAliasMap.getOrDefault(base, new HashSet<>());
                    aliasVars.forEach(var -> {
                        var.getLoadArrays().forEach(loadArray -> {workList.add((Node) loadArray);});
                    });
                }
            });
        }
    }
}
