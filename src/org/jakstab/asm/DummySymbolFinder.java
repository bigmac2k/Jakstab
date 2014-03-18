/*
 * Copyright 2002 Sun Microsystems, Inc.  All Rights Reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Sun Microsystems, Inc., 4150 Network Circle, Santa Clara,
 * CA 95054 USA or visit www.sun.com if you need additional information or
 * have any questions.
 *  
 */

/* 
 * Original code for this class taken from the Java HotSpot VM. 
 * Modified for use with the Jakstab project. All modifications 
 * Copyright 2007-2014 Johannes Kinder <jk@jakstab.org>
 */

package org.jakstab.asm;

public class DummySymbolFinder implements SymbolFinder {
	
	private static SymbolFinder INSTANCE = new DummySymbolFinder();
	
	public static SymbolFinder getInstance() {
		return INSTANCE;
	}
	
	private DummySymbolFinder() {}

	public String getSymbolFor(long address) {
		return "0x" + Long.toHexString(address);
	}

	public String getSymbolFor(AbsoluteAddress va) {
		return va.toString();
	}

	public boolean hasSymbolFor(AbsoluteAddress va) {
		return false;
	}

	public AbsoluteAddress getAddressFor(String symbol) {
		return null;
	}
}
