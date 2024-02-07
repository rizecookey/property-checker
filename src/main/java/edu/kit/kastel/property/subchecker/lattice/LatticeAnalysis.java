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

import edu.kit.kastel.property.packing.PackingClientAnalysis;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

public final class LatticeAnalysis extends PackingClientAnalysis<LatticeValue, LatticeStore, LatticeTransfer> {

    public LatticeAnalysis(
            BaseTypeChecker checker,
            LatticeAnnotatedTypeFactory factory) {
        super(checker, factory);
    }

    @Override
    public LatticeStore createEmptyStore(boolean sequentialSemantics) {
        return new LatticeStore(this, sequentialSemantics);
    }
    
    @Override
    public @Nullable LatticeValue createAbstractValue(
            AnnotationMirrorSet annotations,
            TypeMirror underlyingType) {
        if (!CFAbstractValue.validateSet(annotations, underlyingType, atypeFactory)) {
            return null;
        }
        return new LatticeValue(this, annotations, underlyingType);
    }

	@Override
	public LatticeStore createCopiedStore(LatticeStore s) {
		return new LatticeStore(s);
	}
}
