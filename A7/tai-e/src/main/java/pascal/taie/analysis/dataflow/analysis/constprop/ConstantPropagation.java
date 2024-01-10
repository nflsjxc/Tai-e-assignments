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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.concurrent.atomic.AtomicBoolean;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // Done - finish me
        CPFact boundaryfact = new CPFact();
        for(Var param: cfg.getIR().getParams())
        {
            if(canHoldInt(param))
            {
                // For entry method parameters, they are not constants, depending on the input
                boundaryfact.update(param, Value.getNAC());
            }
        }
        return boundaryfact;
    }

    @Override
    public CPFact newInitialFact() {
        // Done - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // Done - finish me - Done (Join)
        fact.forEach((var, value) -> {
            target.update(var, meetValue(value, target.get(var)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // Done - finish me
        if(v1.isUndef()) return v2;
        if(v2.isUndef()) return v1;
        if(v1.isNAC() || v2.isNAC()) return Value.getNAC();
        assert (v1.isConstant() && v2.isConstant());
        if(v1 == v2) return Value.makeConstant(v1.getConstant()); else return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // Done - finish me
        AtomicBoolean changed = new AtomicBoolean(false);
        in.forEach(((var, value) -> {
            if (out.update(var, value)) {
                changed.set(true);
            }
        }));
        if(stmt instanceof DefinitionStmt<?,?> s)
        {
            if(s.getLValue() instanceof Var var && canHoldInt(var))
            {
                Value old_val = in.get(var);
                Value new_val = evaluate(s.getRValue(), in);
                if(old_val != new_val)changed.set(true);
                out.update(var, new_val);
            }
        }
        return changed.get();
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */

    public static Value evaluate(Exp exp, CPFact in) {
        // Done - finish me
        //Expression Case 1: x=c
        if(exp instanceof IntLiteral e)
        {
            return Value.makeConstant(e.getValue());
        }

        //Expression Case 2: x=y
        if(exp instanceof Var var)
        {
//            System.out.println("Debug at evaluate: " + exp);
            return in.get(var);
        }

        //Expression Case 3: x=y op z
        if (exp instanceof BinaryExp bexp)
        {
            Var y = bexp.getOperand1(), z = bexp.getOperand2();

            //IMPORTANT: NAC/0 still undef!
            if(in.get(z).isConstant() && in.get(z).getConstant() == 0 && bexp.getOperator() instanceof ArithmeticExp.Op arithop)
            {
                if(arithop == ArithmeticExp.Op.DIV || arithop == ArithmeticExp.Op.REM)
                {
                    return Value.getUndef();
                }
            }

            //const op const
            if (in.get(y).isConstant() && in.get(z).isConstant())
            {
                int y_val = in.get(y).getConstant(), z_val = in.get(z).getConstant();
                //Arithmetic
                if (bexp instanceof ArithmeticExp arithexp)
                {
                    switch (arithexp.getOperator())
                    {
                        case ADD -> {
                            return Value.makeConstant(y_val + z_val);
                        }
                        case SUB -> {
                            return Value.makeConstant(y_val - z_val);
                        }
                        case MUL -> {
                            return Value.makeConstant(y_val * z_val);
                        }
                        case DIV -> {
                            return Value.makeConstant(y_val / z_val);
                        }
                        case REM -> {
                            return Value.makeConstant(y_val % z_val);
                        }
                    }
                }
                //Condition
                if(bexp instanceof ConditionExp condexp)
                {
                    switch (condexp.getOperator())
                    {
                        case EQ -> {
                            return Value.makeConstant(y_val == z_val ? 1 : 0);
                        }
                        case NE -> {
                            return Value.makeConstant(y_val != z_val ? 1 : 0);
                        }
                        case LT -> {
                            return Value.makeConstant(y_val < z_val ? 1 : 0);
                        }
                        case GT -> {
                            return Value.makeConstant(y_val > z_val ? 1 : 0);
                        }
                        case LE -> {
                            return Value.makeConstant(y_val <= z_val ? 1 : 0);
                        }
                        case GE -> {
                            return Value.makeConstant(y_val >= z_val ? 1 : 0);
                        }
                    }
                }

                //Shift
                if (bexp instanceof ShiftExp shiftexp)
                {
                    switch (shiftexp.getOperator())
                    {
                        case SHL -> {
                            return Value.makeConstant(y_val << z_val);
                        }
                        case SHR -> {
                            return Value.makeConstant(y_val >> z_val);
                        }
                        case USHR -> {
                            return Value.makeConstant(y_val >>> z_val);
                        }
                    }
                }

                //Bitwise
                if (bexp instanceof BitwiseExp bitwiseexp)
                {
                    switch (bitwiseexp.getOperator())
                    {
                        case AND -> {
                            return Value.makeConstant(y_val & z_val);
                        }
                        case OR -> {
                            return Value.makeConstant(y_val | z_val);
                        }
                        case XOR -> {
                            return Value.makeConstant(y_val ^ z_val);
                        }
                    }
                }
            }

            //y=NAC / z=NAC
            if(in.get(y).isNAC() || in.get(z).isNAC()) return Value.getNAC();

            //Undef otherwise
            return Value.getUndef();

        }

        // Expression Case 4: instanceField
        if (exp instanceof InstanceFieldAccess instanceExp) {

        }

        //Expression Case 5: staticField
        if (exp instanceof StaticFieldAccess staticExp) {

        }

        //Expression Case 6: array
        if (exp instanceof ArrayAccess arrayExp) {

        }

        //Done: Shouldn't reach? Answer: load field: Point a, x=a.f, just like boundary fact
        //TODO double check this
        return Value.getNAC();
    }
}
