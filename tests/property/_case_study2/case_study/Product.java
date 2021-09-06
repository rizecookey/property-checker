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
package case_study;

import edu.kit.iti.checker.property.subchecker.lattice.case_study_qual.*;
import edu.kit.iti.checker.property.checker.qual.*;

public class Product {
    
    public final String title;
    public final @Interval(min="0", max="2147483647") int price;
    public final @Interval(min="0", max="18") int ageRestriction;

    @JMLClause("ensures this.title == title && this.price == price && this.ageRestriction == ageRestriction")
    @JMLClause("assignable \\nothing")
    // :: error: inconsistent.constructor.type
    public @AllowedFor(age="ageRestriction") Product(
            String title,
            @Interval(min="0", max="2147483647") int price,
            @Interval(min="0", max="18") int ageRestriction) {
        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
    }

    @JMLClause("ensures \result.title == title && \result.price == price && \result.ageRestriction == 18")
    @JMLClause("assignable \\nothing")
    public static @AllowedFor(age="18") Product product18(
            String title,
            @Interval(min="0", max="2147483647") int price) {
        // :: error: return.type.incompatible
        return new Product(title, price, 18);
    }

    @JMLClause("ensures \result.title == title && \result.price == price && \result.ageRestriction == 6")
    @JMLClause("assignable \\nothing")
    public static @AllowedFor(age="6") Product product6(
            String title,
            @Interval(min="0", max="2147483647") int price) {
        // :: error: return.type.incompatible
        return new Product(title, price, 6);
    }
}
