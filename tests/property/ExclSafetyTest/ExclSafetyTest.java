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
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

public abstract class ExclSafetyTest {
    
    @ExclMut @Length(min="1", max="3") List f0;
    @Immutable @Length(min="1", max="5") List f1;
    
    // :: error: type.invalid
    @ShrMut @Length(min="1", max="5") List f2;
    // :: error: type.invalid
    @ReadOnly @Length(min="1", max="5") List f3;
    
    @ExclMut @UnknownLength List f5;
    @Immutable @UnknownLength List f6;
    @ShrMut @UnknownLength List f7;
    @ReadOnly @UnknownLength List f8;
    
    // :: error: initialization.fields.uninitialized
    public ExclSafetyTest() { }
    
    public static void foo() {
        @ExclMut @Length(min="1", max="3") List l0;
        @Immutable @Length(min="1", max="5") List l1;
        
        // :: error: type.invalid
        @ShrMut @Length(min="1", max="5") List l2;
        // :: error: type.invalid
        @ReadOnly @Length(min="1", max="5") List l3;
        
        @ExclMut @UnknownLength List l5;
        @Immutable @UnknownLength List l6;
        @ShrMut @UnknownLength List l7;
        @ReadOnly @UnknownLength List l8;
    }
}
