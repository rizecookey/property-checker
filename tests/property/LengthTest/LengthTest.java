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

public abstract class LengthTest {
    public static void foo0(
            @Immutable @Length(min="2", max="2") List arg0,
            @Immutable @Length(min="2", max="5") List arg1) {
        @Immutable @Length(min="1", max="3") List l0 = arg0;
        @Immutable @Length(min="1", max="5") List l1 = arg1;
        
        // :: error: assignment.type.incompatible
        @Immutable @Length(min="3", max="5") List l2 = arg1;
    }
    
    public static void foo1(
            @Immutable @Length(min="2", max="2") List arg0,
            @Immutable @Length(min="2", max="5") List arg1) {
        List l0 = arg0;
        @Immutable @Length(min="2", max="2") List l1 = l0;
        
        foo0(arg0, arg1);
        
        // :: error: argument.type.incompatible
        bar(arg0, arg1, true);
        
        // :: error: argument.type.incompatible
        @Immutable @Length(min="2", max="3") List l2 = bar(arg0, arg1, true);
        
        // :: error: argument.type.incompatible :: error: assignment.type.incompatible
        @Immutable @Length(min="2", max="2") List l3 = bar(arg0, arg1, true);
    }

    public static @Immutable @Length(min="2", max="3") List bar(
            @Immutable @Length(min="2", max="2") List arg0,
            @Immutable @Length(min="3", max="3") List arg1,
            boolean b) {
        return b ? arg0 : arg1;
    }

    public static @Length(min="2", max="3") List baz0(
            @Length(min="2", max="2") List arg0,
            @Length(min="3", max="3") List arg1,
            boolean b) {
        if (b) {
            return arg0;
        } else {
            return arg1;
        }
    }

    public static @Immutable @Length(min="2", max="3") List baz1(
            @Immutable @Length(min="2", max="2") List arg0,
            @Immutable @Length(min="3", max="3") List arg1,
            boolean b) {
        List result;
        if (b) {
            result = arg0;
        } else {
            result = arg1;
        }
        return result;
    }

    //public static void foo2(@Length(min="2", max="2") List arg0, @Length(min="3", max="3") List arg1, boolean b) {
    //   List l0 = b ? arg0 : arg1;
    //   @Length(min="2", max="3") List l1 = l0;
    //}
    
    public abstract @Immutable @Length(min="2", max="3") List override0(
            @Immutable @Length(min="2", max="3") List a);
    
    public abstract @Immutable @Length(min="2", max="3") List override1();
    
    public void override2(@Immutable @Length(min="2", max="3") List a) { }
}

abstract class SubLengthTest extends LengthTest {

    public abstract @Immutable @Length(min="2", max="2") List override0(
            @Immutable @Length(min="1", max="4") List a);
    
    // :: error: override.return.invalid
    public abstract @Immutable @Length(min="2", max="6") List override1();
    
    // :: error: override.param.invalid
    public void override2(@Immutable @Length(min="1", max="1") List a) { }
}