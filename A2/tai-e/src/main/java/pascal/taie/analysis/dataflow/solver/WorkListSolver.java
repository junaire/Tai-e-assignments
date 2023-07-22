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

package pascal.taie.analysis.dataflow.solver;

import pascal.taie.analysis.dataflow.analysis.DataflowAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.cfg.CFG;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.List;
import java.util.Queue;

class WorkListSolver<Node, Fact> extends Solver<Node, Fact> {

    WorkListSolver(DataflowAnalysis<Node, Fact> analysis) {
        super(analysis);
    }

    @Override
    protected void doSolveForward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        Queue<Node> workList = new ArrayDeque<>(cfg.getNodes());
        while (!workList.isEmpty()) {
            Node node = workList.poll();
            if (cfg.isEntry(node)) {
                continue;
            }

            // Meet all predecessors.
            List<Node> predecessors = new ArrayList<>(cfg.getPredsOf(node));
            Fact inFact = (Fact) ((CPFact) result.getOutFact(predecessors.get(0))).copy();
            for (int i = 1; i < predecessors.size(); ++i) {
                analysis.meetInto(inFact, result.getOutFact(predecessors.get(i)));
            }
            result.setInFact(node, inFact);

            boolean changed = analysis.transferNode(node, result.getInFact(node), result.getOutFact(node));

            if (changed) {
                workList.addAll(cfg.getSuccsOf(node));
            }
        }

    }

    @Override
    protected void doSolveBackward(CFG<Node> cfg, DataflowResult<Node, Fact> result) {
        throw new UnsupportedOperationException();
    }
}
