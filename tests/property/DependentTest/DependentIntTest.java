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

class A {
    
    public static final int MIN = 1, MAX = 1;

    public static void foo0(@Interval(min="2", max="2") int arg0, @Interval(min="2", max="5") int arg1) {

        // :: error: assignment.type.incompatible
        @Interval(min="MIN", max="MAX") int x = new B().field;
        
        // :: error: assignment.type.incompatible
        @Interval(min="1", max="1 + 2") int l0 = arg0;
        @Interval(min="1", max="5") int l1 = arg1;
        
        final int MAX = 5;
        // :: error: assignment.type.incompatible
        @Interval(min="1", max="MAX") int l2 = arg1;
        
        // :: error: assignment.type.incompatible
        l0 = l2;
    }
}

// :: error: initialization.fields.uninitialized
class B {
    
    public static final int MIN = 0, MAX = 1;

    public @Interval(min="MIN", max="MAX") int field;
}
