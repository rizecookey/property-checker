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

// Dependent types helper for lattice type systems that automatically viewpoint-adapts dependent types based
// on where they appear. The basis for this is a customised implementation of DependentTypesHelper that considers all
// string fields on annotations possible Java Expressions (the checker framework upstream default: only String array
// fields annotated with @JavaExpression are considered for viewpoint adaptation)
public final class LatticeDependentTypesHelper extends DependentTypesHelper {

    public LatticeDependentTypesHelper(LatticeAnnotatedTypeFactory factory) {
        super(factory);
    }
}
