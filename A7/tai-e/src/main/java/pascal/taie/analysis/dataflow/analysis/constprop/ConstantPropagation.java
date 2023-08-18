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
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.ArrayMap;
import pascal.taie.util.collection.ArraySet;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    private Map<JField, Set<Value>> storeFieldValueMap;

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
        storeFieldValueMap = new ArrayMap<>();
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
            if (canHoldInt(var)) {
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var var : fact.keySet()) {
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        if (v1.getConstant() == v2.getConstant()) {
            return Value.makeConstant(v1.getConstant());
        }
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact inCopy = in.copy();
        if (stmt instanceof LoadField loadField) {
            if (loadField.isStatic()) {
                Var var = loadField.getLValue();
                JField field = loadField.getFieldRef().resolve();
                Value result = inCopy.get(var);
                for (Value storeValue : storeFieldValueMap.getOrDefault(field, new ArraySet<>())) {
                    result = meetValue(result, storeValue);
                }
                inCopy.update(var, result);
            }
        } else if (stmt instanceof StoreField storeField) {
            if (storeField.isStatic()) {
                Var var = storeField.getRValue();
                if (canHoldInt(var)) {
                    JField field = storeField.getFieldRef().resolve();
                    Value value = inCopy.get(var);
                    Set<Value> values = storeFieldValueMap.get(field);
                    if (values == null) {
                        storeFieldValueMap.put(field, new ArraySet<>());
                    } else {
                        values.add(value);
                        storeFieldValueMap.put(field, values);
                    }
                }
            }
        } else if (stmt instanceof DefinitionStmt<?, ?> definitionStmt) {
            LValue lv = definitionStmt.getLValue();
            RValue rv = definitionStmt.getRValue();
            if (lv instanceof Var var) {
                if (canHoldInt(var)) {
                    inCopy.update(var, evaluate(rv, in));
                    return out.copyFrom(inCopy);
                }
            }
        }
        return out.copyFrom(inCopy);
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
        if (exp instanceof IntLiteral intLiteral) {
            return Value.makeConstant(intLiteral.getValue());
        }
        if (exp instanceof Var var) {
            return in.get(var);
        }
        if (exp instanceof StaticField staticField) {
            staticField.getField();
        }

        Value result = Value.getNAC();

        if (exp instanceof BinaryExp binaryExp) {
            Var op1 = binaryExp.getOperand1(), op2 = binaryExp.getOperand2();
            Value v1 = in.get(op1);
            Value v2 = in.get(op2);


            if (v1.isConstant() && v2.isConstant()) {
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    switch (arithmeticExp.getOperator()) {
                        case ADD -> result = Value.makeConstant(v1.getConstant() + v2.getConstant());
                        case MUL -> result = Value.makeConstant(v1.getConstant() * v2.getConstant());
                        case SUB -> result = Value.makeConstant(v1.getConstant() - v2.getConstant());
                        case DIV -> {
                            if (v2.getConstant() == 0) {
                                result = Value.getUndef();
                            } else {
                                result = Value.makeConstant(v1.getConstant() / v2.getConstant());
                            }
                        }
                        case REM -> {
                            if (v2.getConstant() == 0) {
                                result = Value.getUndef();
                            } else {
                                result = Value.makeConstant(v1.getConstant() % v2.getConstant());
                            }
                        }
                    }
                } else if (exp instanceof BitwiseExp bitwiseExp) {
                    switch (bitwiseExp.getOperator()) {
                        case AND -> result = Value.makeConstant(v1.getConstant() & v2.getConstant());
                        case OR -> result = Value.makeConstant(v1.getConstant() | v2.getConstant());
                        case XOR -> result = Value.makeConstant(v1.getConstant() ^ v2.getConstant());
                    }
                } else if (exp instanceof ConditionExp conditionExp) {
                    switch (conditionExp.getOperator()) {
                        case EQ -> result = Value.makeConstant((v1.getConstant() == v2.getConstant()) ? 1 : 0);
                        case GE -> result = Value.makeConstant((v1.getConstant() >= v2.getConstant()) ? 1 : 0);
                        case GT -> result = Value.makeConstant((v1.getConstant() > v2.getConstant()) ? 1 : 0);
                        case LE -> result = Value.makeConstant((v1.getConstant() <= v2.getConstant()) ? 1 : 0);
                        case LT -> result = Value.makeConstant((v1.getConstant() < v2.getConstant()) ? 1 : 0);
                        case NE -> result = Value.makeConstant((v1.getConstant() != v2.getConstant()) ? 1 : 0);
                    }
                } else if (exp instanceof ShiftExp shiftExp) {
                    switch (shiftExp.getOperator()) {
                        case SHL -> result = Value.makeConstant(v1.getConstant() << v2.getConstant());
                        case SHR -> result = Value.makeConstant(v1.getConstant() >> v2.getConstant());
                        case USHR -> result = Value.makeConstant(v1.getConstant() >>> v2.getConstant());
                    }
                } else {
                    result = Value.getUndef();
                }
            } else if (v1.isNAC() || v2.isNAC()) {
                if (exp instanceof ArithmeticExp arithmeticExp) {
                    ArithmeticExp.Op op = arithmeticExp.getOperator();
                    if (op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM) {
                        if (v2.isConstant() && v2.getConstant() == 0) {
                            result = Value.getUndef();
                        }

                    }
                }
            } else {
                result = Value.getUndef();
            }
        } else if (exp instanceof LoadField loadField) {
            loadField.getFieldRef();
        }
        return result;
    }
}
