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
package edu.kit.kastel.property.subchecker.lattice;

import org.checkerframework.framework.util.dependenttypes.DependentTypesHelper;

public final class LatticeDependentTypesHelper extends DependentTypesHelper {

    // TODO implement this to handle our custom notion of dependent types (adjustment in checker framework necessary)
    //  and remove any ad-hoc viewpoint adaptation done in store, transfer or visitor (should all happen implicitly)

    public LatticeDependentTypesHelper(LatticeAnnotatedTypeFactory factory) {
        super(factory);
    }
}
