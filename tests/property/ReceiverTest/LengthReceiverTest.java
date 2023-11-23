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
import java.util.List;

import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

public abstract class LengthReceiverTest implements List {

    public void method(
            @Length(min="1", max="1") @Immutable LengthReceiverTest this,
            @Length(min="2", max="2") @Immutable LengthReceiverTest that) { }

    public void foo(
            @Immutable LengthReceiverTest this,
            @Length(min="1", max="1") @Immutable LengthReceiverTest a,
            @Length(min="2", max="2") @Immutable LengthReceiverTest b) {
        a.method(b);

        // :: error: argument.type.incompatible
        a.method(a);

        // :: error: method.invocation.invalid :: error: argument.type.incompatible
        b.method(a);

        // :: error: method.invocation.invalid
        b.method(b);

        // :: error: method.invocation.invalid :: error: argument.type.incompatible
        this.method(a);

        // :: error: method.invocation.invalid
        this.method(b);
    }
}
