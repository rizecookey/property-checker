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

public abstract class LengthInitTest {
    
    public @Immutable @Length(min="1", max="3") List i2;
    public @Immutable @Length(min="1", max="1") List i3;
    
    public @Immutable @Length(min="1", max="3") List i4;

    // :: error: initialization.fields.uninitialized
    public LengthInitTest(@Immutable @Length(min="1", max="3") List arg) {
        i2 = arg;
        
        // :: error: assignment.type.incompatible
        i3 = arg;
    }
}
