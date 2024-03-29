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
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;
import java.util.HashSet;
import java.util.Queue;
import java.util.LinkedList;
import pascal.taie.util.collection.Pair;

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
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        Set<Stmt> liveCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        Queue<Stmt> queue = new LinkedList<>();
        queue.add(cfg.getEntry());
        // Dead code identification
        while(!queue.isEmpty()) {
            Stmt stmt = queue.poll();
            System.out.println("Queue stmt: "+ "idx: "+stmt.getIndex()+", stmt: " +stmt);
            if(liveCode.contains(stmt))continue;
            // 2. Dead Assignment
            // Process this first because this part may not be added into livecode in 1.1
            if(stmt instanceof AssignStmt<?, ?> assignstmt) { //Assignments
                if(assignstmt.getLValue() instanceof Var lvar && hasNoSideEffect(assignstmt.getRValue())) {
                        if(!liveVars.getOutFact(assignstmt).contains(lvar)) {
                            queue.addAll(cfg.getSuccsOf(assignstmt));
                            continue;
                        }
                }
            }
            //1.1 Control-flow Unreachable Code
            if(!liveCode.add(stmt))continue;//Add stmt to livecode

            // 1.2 Unreachable Branch
            if(stmt instanceof If ifstmt) {//If branches
                // If (x > 0) ...
                Value cond = ConstantPropagation.evaluate(ifstmt.getCondition(), constants.getInFact(ifstmt));
                if(!cond.isConstant()) {
                    queue.addAll(cfg.getSuccsOf(ifstmt));
                    continue;
                }
                // If constant, we need to eliminate dead branch
//                System.out.println("Cond stmt: "+ "idx: "+stmt.getIndex()+", stmt: " +stmt);
                for(Edge<Stmt> edge : cfg.getOutEdgesOf(ifstmt)) {
                    if(edge.getKind() == Edge.Kind.IF_TRUE && cond.getConstant() == 1) {
//                        System.out.println(" Adding: "+ edge.getTarget());
                        queue.add(edge.getTarget());
                    }
                    if(edge.getKind() == Edge.Kind.IF_FALSE && cond.getConstant() == 0) {
//                        System.out.println(" Adding: "+ edge.getTarget());
                        queue.add(edge.getTarget());
                    }
                }
            }
            else if(stmt instanceof SwitchStmt switchstmt) { //Switch branches
                Value cond = ConstantPropagation.evaluate(switchstmt.getVar(), constants.getInFact(switchstmt));
                if(!cond.isConstant()) {
                    queue.addAll(cfg.getSuccsOf(switchstmt));
                    continue;
                }
                // If constant, we need to eliminate dead branch
                boolean hasDefault = true;
                for(Edge<Stmt> edge : cfg.getOutEdgesOf(switchstmt)) {
                    if(edge.isSwitchCase()) {
                        if (edge.getCaseValue() == cond.getConstant()) {
                            hasDefault = false;
                            queue.add(edge.getTarget());
                        }
                    }
                }
                if(hasDefault) {
                    queue.add(switchstmt.getDefaultTarget());
                }
            }
            else {
                //Add successors to queue to identify 1.1 Control-flow Unreachable Code
                System.out.println("Adding " + stmt + " " +cfg.getSuccsOf(stmt));
                queue.addAll(cfg.getSuccsOf(stmt));
            }

        }

        deadCode.addAll(cfg.getNodes());
        deadCode.removeAll(liveCode);
        deadCode.remove(cfg.getExit()); //Sometimes exit is not visited?

        return deadCode;
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
