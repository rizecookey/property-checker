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

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class List {

    final Object element;

    @Nullable
    @Length(len="size - 1")
    final List next;

    @Positive
    final int size;

    @Pure
    @Length(len="rest.size + 1")
    List(Object element, @NonNull List rest) {
        this.element = element;
        this.next = rest;
        this.size = rest.size + 1;
        Packing.pack(this, List.class);
    }

    @Pure
    @Length(len="1")
    List(Object element) {
        this.element = element;
        this.next = null;
        this.size = 1;
        Packing.pack(this, List.class);
    }

    @Pure
    Object nth(@LengthAtLeast(len="i + 1") @ReadOnly List this, int i) {
        return null;
    }

    @Pure
    @NonNull
    @Length(len="this.size + other.size")
    List prependAll(@ReadOnly List this, @ReadOnly List other) {
        return null;
    }
}
