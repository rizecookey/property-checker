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
import edu.kit.iti.checker.property.checker.qual.*;

public class DependentLengthTest {
    public static
    @JMLClause(values={"requires a+c > 0 && b+d > 0"})
    @Length(min="a+c", max="b+d") List
    concat(
            int a, int b, int c, int d,
            @Length(min="a", max="b") List l0, @Length(min="c", max="d") List l1) {
        // :: error: return.type.incompatible
        return null;
    }

    public static void foo(
            @Length(min="1", max="1") List l0,
            @Length(min="2", max="2") List l1) {
        // :: error: assignment.type.incompatible :: error: argument.type.incompatible
        @Length(min="3", max="3") List res = concat(1, 1, 2, 2, l0, l1);
    }
}
