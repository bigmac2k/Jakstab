package org.jakstab.rtl.expressions;

import cc.sven.misc.JavaOrdering;

/**
 * Created by scm on 04.02.16.
 */
public class RTLVariableIsOrdered extends JavaOrdering<RTLVariable> {
    private static final long serialVersionUID = 1L;
    public int compare(RTLVariable x, RTLVariable y) {
        return x.compareTo(y);
    }
}
