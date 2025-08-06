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

import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.packing.PackingClientValue;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Optional;
import java.util.stream.Stream;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeValue extends PackingClientValue<LatticeValue> {

	private final JavaExpression refinement;
	private final List<JavaExpression> refinementParams;

	// TODO: verify that there are no ambiguities when parsing
	//  e.g.: are there situations where LatticeValues originally parsed at field declarations are recreated in a local context?
	protected LatticeValue(
			LatticeAnalysis analysis,
			AnnotationMirrorSet annotations,
			TypeMirror underlyingType) {
		super(analysis, annotations, underlyingType);

		JavaExpression parsedRefinement = null;
		List<JavaExpression> parsedParams = List.of();
		PropertyAnnotation property = toPropertyAnnotation();
		try {
			if (analysis.getLocalTree() != null) {
				// if we have a location where the refinement should be parsed, we parse it
				var localPath = analysis.getTypeFactory().getPath(analysis.getLocalTree());
				parsedRefinement = property.parseRefinement(localPath, analysis.getTypeFactory().getChecker());
				parsedParams = property.parseRefinementParams(localPath, analysis.getTypeFactory().getChecker());
			} else if (analysis.getField() != null) {
				parsedRefinement = property.parseRefinement(analysis.getField(), analysis.getTypeFactory().getChecker());
				parsedParams = property.parseRefinementParams(analysis.getField(), analysis.getTypeFactory().getChecker());
			}
		} catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
			// ignored
		}
		this.refinement = parsedRefinement;
		this.refinementParams = parsedParams;
    }

	public PropertyAnnotation toPropertyAnnotation() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		var anno = factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop());
		return factory.getLattice().getPropertyAnnotation(anno == null ? factory.getTop() : anno);
	}

	/**
	 * Returns the parsed refinement behind this value with the {@code §subject§} variable substituted for the given expression.
	 *
	 * @param subject the subject to insert into the refinement.
	 * @return An empty optional if the refinement couldn't be parsed, otherwise an optional containing the
	 * refinement applied to the subject.
	 */
	public Optional<JavaExpression> getRefinement(JavaExpression subject) {
		return Optional.ofNullable(refinement).map(prop -> viewpointAdapt(prop, List.of(subject)));
	}

	/**
	 * Returns the parsed parameters of the refinement qualifier behind this value with the {@code §subject§} variable substituted for the given expression.
	 *
	 * @param subject the subject to insert into the refinement.
	 * @return the parameters of the refinement qualifier applied to the subject
	 */
	public Stream<JavaExpression> getRefinementParams(JavaExpression subject) {
		return refinementParams.stream().map(p -> viewpointAdapt(p, List.of(subject)));
	}

	public boolean isParsed() {
		return refinement != null;
	}

	public boolean onlyLiterals() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return factory.getLattice().getEvaluatedPropertyAnnotation(
				factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop())) != null;
	}

}
