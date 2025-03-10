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
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class NullnessContractsTest {

    @NonNull Object field;

    public NullnessContractsTest() {
        this.init();
    }

    @EnsuresNonNull("field")
    @EnsuresInitialized("this")
    public void init(@Unique @UnderInitialization NullnessContractsTest this) {
        this.field = new Object();
    }

    @RequiresNonNull("field") @RequiresMaybeAliased("field")
    @EnsuresInitialized("this")
    public void emptyInit(@Unique @UnderInitialization NullnessContractsTest this) {}

    @EnsuresInitialized("#1")
    public static void conditionalInit(@Unique @UnderInitialization NullnessContractsTest arg) {
        if (!arg.isFieldCommitted()) {
            arg.init();
        } else {
            // :: error: contracts.precondition.not.satisfied
            arg.emptyInit();
        }
    }

    @EnsuresNonNullIf(result = true, expression = "field")
    @Pure
    public boolean isFieldCommitted(@Unique @UnknownInitialization NullnessContractsTest this) {
        return this.field != null;
    }
}
