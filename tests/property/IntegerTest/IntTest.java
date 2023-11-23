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
import edu.kit.kastel.property.subchecker.lattice.qual.*;

public class IntTest {
    
    // :: error: assignment.type.incompatible
    @Interval(min="1", max="2") int field = 3;    
    
    public static void foo0(@Interval(min="2", max="2") int arg0, @Interval(min="2", max="5") int arg1) {
        @Interval(min="1", max="3") int l0 = arg0;
        @Interval(min="1", max="5") int l1 = arg1;
        
        // :: error: assignment.type.incompatible
        @Interval(min="1", max="2") int l2 = arg1;
        
        // This does not work yet. It would require a contract for the + operator.
        // :: error: assignment.type.incompatible
        @Interval(min="4", max="7") int l3 = arg0 + arg1;
        
        // :: error: assignment.type.incompatible
        @Interval(min="2", max="5") int l4 = arg0 + arg1;
        // :: error: assignment.type.incompatible
        @Interval(min="2", max="2") int l5 = arg0 + arg1;
        
        @Interval(min="4", max="7") @Remainder(remainder="1", modulus="4") int lit0 = 5;
        
        // :: error: assignment.type.incompatible
        lit0 = 6;
        
        @Interval(min="4", max="7") int lit1 = 5;
        
        // :: error: unary.increment.type.incompatible
        ++lit1;
    }
    
    public static void foo1(
            @Remainder(remainder="1", modulus="6") int arg0,
            @Remainder(remainder="4", modulus="6") int arg1) {
        @Remainder(remainder="1", modulus="3") int a = arg0;
        a = arg1;
    }
    
    public static void foo2(@Remainder(remainder="1", modulus="6") @Interval(min="1", max="5") int arg0) {
        foo1(arg0, 4);
        
        // :: error: argument.type.incompatible
        foo1(arg0, 0);
        
        // :: error: assignment.type.incompatible
        @Remainder(remainder="1", modulus="12") @Interval(min="1", max="5") int a = arg0;

        // :: error: assignment.type.incompatible
        @Remainder(remainder="1", modulus="6") @Interval(min="3", max="3") int b = arg0;

        // :: error: assignment.type.incompatible :: error: assignment.type.incompatible
        @Remainder(remainder="1", modulus="12") @Interval(min="3", max="3") int c = arg0;
        
        @Remainder(remainder="1", modulus="6") @Interval(min="1", max="5") int d = arg0;
    }
}
