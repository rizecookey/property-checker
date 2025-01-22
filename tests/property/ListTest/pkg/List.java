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
package pkg;

import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

public class List {

    private final Object element;

    @Length(len="size - 1")
    private final List next;

    @Positive
    public final int size;

    @Length(len="rest.size + 1")
    public List(Object element, List rest) {
        this.element = element;
        this.next = rest;
        this.size = (rest == null ? 0 : rest.size) + 1;
    }

    @Length(len="size + 1")
    public List push(@ReadOnly List this, Object element) {
        return new List(element, this);
    }

    @Length(len="size - 1")
    public List pop(@ReadOnly List this) {
        return next;
    }

    public Object peekNth(@ReadOnly List this, @Interval(min="0",max="size-1") int index) {
        List pos = this;
        for (int i = 0; i < index; i++) {
            pos = pos.pop();
        }
        return pos.element;
    }

    @Length(len="times")
    public static List repeat(Object element, @Positive int times) {
        List result = null;
        for (int i = 0; i < times; i++) {
            result = new List(element, result);
        }
        return result;
    }
}

// FIXME debug test errors
class ListTest {
    void foo(@Interval(min="0", max="10000") int input) {
        @Length(len="input * 2 - 1") List myList = List.repeat("Hi :)", input * 2).pop();
        Object el = myList.push("new").push("value").peekNth(2);
    }
}