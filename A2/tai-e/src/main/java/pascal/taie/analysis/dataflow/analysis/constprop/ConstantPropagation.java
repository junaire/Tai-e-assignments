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
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;

import java.util.List;

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
        CPFact fact = new CPFact();
        List<Var> params = cfg.getIR().getParams();
        for (Var var : params) {
            fact.update(var, Value.getNAC());
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact(Stmt node) {
        CPFact fact = new CPFact();
        if (node instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lValue = definitionStmt.getLValue();
            if (lValue instanceof Var) {
                if (canHoldInt((Var) lValue)) {
                    fact.update((Var) lValue, Value.getNAC());
                }
            }
        }
        return fact;
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : target.keySet()) {
            Value value1 = fact.get(var);
            Value value2 = target.get(var);
            fact.update(var, meetValue(value1, value2));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v1.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef() && v2.isConstant()) {
            return Value.makeConstant(v2.getConstant());
        }
        if (v1.isConstant() && v2.isUndef()) {
            return Value.makeConstant(v1.getConstant());
        }
        int c1 = v1.getConstant();
        int c2 = v2.getConstant();
        if (c1 != c2) {
            return Value.getNAC();
        }
        return Value.makeConstant(c1);
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        boolean changed = false;
        CPFact inCopy = in.copy();
        if (stmt instanceof AssignStmt<?, ?>) {
            LValue lValue = ((AssignStmt<?, ?>) stmt).getLValue();
            if (lValue instanceof Var var) {
                inCopy.remove(var);
                RValue rValue = ((AssignStmt<?, ?>) stmt).getRValue();
                Value value = evaluate(rValue, inCopy);
                assert value != null;
                inCopy.update(var, value);
                changed = true;
            }
        }
        out.copyFrom(inCopy);
        return changed;
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
        if (exp instanceof IntLiteral literal) {
            return Value.makeConstant(literal.getValue());
        } else if (exp instanceof Var var) {
            return in.get(var);
        } else if (exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1();
            Var op2 = binaryExp.getOperand2();
            Value v1 = in.get(op1);
            Value v2 = in.get(op2);

            if (v1.isConstant() && v2.isConstant()) {
                int data = 0;
                if (binaryExp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD:
                            data = v1.getConstant() + v2.getConstant();
                            break;
                        case SUB:
                            data = v1.getConstant() - v2.getConstant();
                            break;
                        case MUL:
                            data = v1.getConstant() * v2.getConstant();
                            break;
                        case DIV: {
                            if (v2.getConstant() == 0) {
                                return Value.getNAC();
                            }
                            data = v1.getConstant() / v2.getConstant();
                            break;
                        }
                    }
                } else if (binaryExp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL:
                            data = v1.getConstant() << v2.getConstant();
                            break;
                        case SHR:
                            data = v1.getConstant() >> v2.getConstant();
                            break;
                        case USHR:
                            data = v1.getConstant() >>> v2.getConstant();
                            break;
                    }
                } else if (binaryExp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ:
                            data = v1.getConstant() == v2.getConstant() ? 1 : 0;
                            break;
                        case NE:
                            data = v1.getConstant() != v2.getConstant() ? 1 : 0;
                            break;
                        case LT:
                            data = v1.getConstant() < v2.getConstant() ? 1 : 0;
                            break;
                        case GT:
                            data = v1.getConstant() > v2.getConstant() ? 1 : 0;
                            break;
                        case LE:
                            data = v1.getConstant() <= v2.getConstant() ? 1 : 0;
                            break;
                        case GE:
                            data = v1.getConstant() >= v2.getConstant() ? 1 : 0;
                            break;
                    }
                } else if (binaryExp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case OR:
                            data = v1.getConstant() | v2.getConstant();
                            break;
                        case AND:
                            data = v1.getConstant() & v2.getConstant();
                            break;
                        case XOR:
                            data = v1.getConstant() ^ v2.getConstant();
                            break;
                    }
                } else {
                    throw new UnsupportedOperationException();
                }
                return Value.makeConstant(data);
            } else if (v1.isNAC() || v2.isNAC()) {
                return Value.getNAC();
            }
            return Value.getUndef();
        }
        return null;
    }
}
