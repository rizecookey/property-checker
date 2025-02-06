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

import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.packing.PackingClientValue;
import org.apache.commons.lang3.function.FailableFunction;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.AnnotationMirrorSet;

public final class LatticeValue extends PackingClientValue<LatticeValue> {

	private JavaExpression refinement;

	protected LatticeValue(
			LatticeAnalysis analysis,
			AnnotationMirrorSet annotations,
			TypeMirror underlyingType) {
		super(analysis, annotations, underlyingType);
	}

	public PropertyAnnotation toPropertyAnnotation() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		var anno = factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop());
		return factory.getLattice().getPropertyAnnotation(anno);
	}

	// TODO move refinement parsing from here to analysis class (need to figure out how to pass along subject and tree)
	public void computeRefinement(
			String subject,
			FailableFunction<String, JavaExpression, JavaExpressionParseUtil.JavaExpressionParseException> parser
	) {
		if (this.refinement != null) {
			return;
		}

		String refinement = toPropertyAnnotation().combinedRefinement(subject);
        try {
            this.refinement = parser.apply(refinement);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            // TODO: logging
        }
    }

	public boolean onlyLiterals() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return factory.getLattice().getEvaluatedPropertyAnnotation(
				factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop())) != null;
	}

	@Nullable
	public JavaExpression getRefinement() {
		return refinement;
	}
}
