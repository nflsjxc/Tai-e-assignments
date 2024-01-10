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
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of 2-object sensitivity.
 */
public class _2ObjSelector implements ContextSelector {

    @Override
    public Context getEmptyContext() {
        return ListContext.make();
    }

    @Override
    public Context selectContext(CSCallSite callSite, JMethod callee) {
        // Done - finish me
        // In object and type sensitivity, the convention of handling static methods is to directly use
        // the caller context as the context of the callee (namely, the target method of the static call).
        return callSite.getContext();
    }

    @Override
    public Context selectContext(CSCallSite callSite, CSObj recv, JMethod callee) {
        // Done - finish me
        // Notice call's context may be different from object's context - processcall(c:x, c':o)
        Context callerContext = recv.getContext();
        int len = callerContext.getLength();
        Context calleeContext;
        if(len >= 1)
            calleeContext = ListContext.make(callerContext.getElementAt(len-1), recv.getObject());
        else
            calleeContext = ListContext.make(recv.getObject());
        return calleeContext;
    }

    @Override
    public Context selectHeapContext(CSMethod method, Obj obj) {
        // Done - finish me
        // it is used for x=new T(), so we just use caller's current context
        // Only for call we need to recalculate context
        Context currentContext = method.getContext();
        int len = currentContext.getLength();
        Context newContext;
        if(len >= 1)
            newContext = ListContext.make(currentContext.getElementAt(len-1));
        else
            newContext = ListContext.make();
        return newContext;
    }
}
