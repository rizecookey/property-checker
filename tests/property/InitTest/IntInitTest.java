/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
import java.util.*;
import edu.kit.iti.checker.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class IntInitTest {
    
    int unannotated;
    @Remainder(remainder="0", modulus="2") int even;
    @Remainder(remainder="1", modulus="2") int odd;
    
    public IntInitTest() {
        helper();
        
        even = 2;
        odd = 1;
        
        // :: error: method.invocation.invalid
        nonHelper();
    }

    public @Remainder(remainder="0", modulus="2") int helper(@UnknownInitialization IntInitTest this) {
    	// :: error: return.type.incompatible
        return even;
    }

    public @Remainder(remainder="0", modulus="2") int nonHelper() {
    	return even;
    }
}
