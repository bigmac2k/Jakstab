package org.jakstab.analysis;

import cc.sven.misc.JavaOrdering;

/**
 * Created by scm on 05.02.16.
 */
public class MemoryRegionIsOrdered extends JavaOrdering<MemoryRegion> {
    public int compare(MemoryRegion a, MemoryRegion b) { return a.compareTo(b); }
}
