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
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;


public class AnnotatedConstructorTest {
    
    // :: error: inconsistent.constructor.type
    public @B AnnotatedConstructorTest() {
        super();
    }

    public void foo(@Immutable @B AnnotatedConstructorTest arg) {
        @Immutable AnnotatedConstructorTest b = new AnnotatedConstructorTest();
        arg = b;
        
        @Immutable @A AnnotatedConstructorTest a = new AnnotatedConstructorTest();
        
        // :: error: assignment.type.incompatible
        @Immutable @D AnnotatedConstructorTest d = b;
    }
}

class SubClass extends AnnotatedConstructorTest {

    public SubClass() {
        super();
    }

    // :: error: inconsistent.constructor.type
    public @D SubClass(int i) {
        super();
    }
}