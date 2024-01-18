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

package pascal.taie.analysis.pta.core.cs.selector;

import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;

import java.util.List;

/**
 * Implementation of 2-call-site sensitivity.
 */
public class _2CallSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // Done - finish me
        Context callerContext = callSite.getContext();
        int len = callerContext.getLength();
        Context calleeContext;
        if(len >= 1)
            calleeContext = ListContext.make(callerContext.getElementAt(len-1), callSite.getCallSite());
        else
            calleeContext = ListContext.make(callSite.getCallSite());
        return calleeContext;
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // Done - finish me
        return selectContext(callSite, callee);
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // Done - finish me
        // it is used for x=new T(), so we just use T's context
        // Only for call we need to recalculate context
        Context callerContext = method.getContext();
        int len = callerContext.getLength();
        Context calleeContext;
        if(len >= 1)
            calleeContext = ListContext.make(callerContext.getElementAt(len-1));
        else
            calleeContext = ListContext.make();
        return calleeContext;
    }
}
