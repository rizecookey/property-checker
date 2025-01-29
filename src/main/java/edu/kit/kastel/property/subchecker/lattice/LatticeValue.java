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

import javax.lang.model.type.TypeMirror;

import edu.kit.kastel.property.packing.PackingClientValue;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.javacutil.AnnotationMirrorSet;

public final class LatticeValue extends PackingClientValue<LatticeValue> {

	// TODO: add modifiable "dependents" field to keep track of who depends on this value

	protected LatticeValue(
			CFAbstractAnalysis<LatticeValue, ?, ?> analysis,
			AnnotationMirrorSet annotations,
			TypeMirror underlyingType) {
		super(analysis, annotations, underlyingType);
	}
}
