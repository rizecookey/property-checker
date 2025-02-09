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

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;

import com.sun.source.tree.VariableTree;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.packing.PackingClientValue;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import java.util.List;
import java.util.Optional;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeValue extends PackingClientValue<LatticeValue> {

	private final JavaExpression property;

	// TODO: verify that there are no ambiguities when parsing
	//  e.g.: are there situations where LatticeValues originally parsed at field declarations are recreated in a local context?
	protected LatticeValue(
			LatticeAnalysis analysis,
			AnnotationMirrorSet annotations,
			TypeMirror underlyingType) {
		super(analysis, annotations, underlyingType);
		var tree = analysis.getPosition();
		JavaExpression parsed = null;
		if (tree != null) {
			// if we have a location where the refinement should be parsed, we parse it
			PropertyAnnotation property = toPropertyAnnotation();
			var element = TreeUtils.elementFromTree(tree);
			try {
				if (element instanceof VariableElement field && field.getKind() == ElementKind.FIELD) {
					parsed = property.parseRefinement(field, analysis.getTypeFactory().getChecker());
				} else {
					var localPath = analysis.getTypeFactory().getPath(tree);
					parsed = property.parseRefinement(localPath, analysis.getTypeFactory().getChecker());
				}
			} catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                // ignored
            }
        }
		this.property = parsed;
    }

	public PropertyAnnotation toPropertyAnnotation() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		var anno = factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop());
		return factory.getLattice().getPropertyAnnotation(anno == null ? factory.getTop() : anno);
	}

	public Optional<JavaExpression> getProperty(JavaExpression subject) {
		return Optional.ofNullable(property).map(prop -> viewpointAdapt(prop, List.of(subject)));
	}

	public boolean isParsed() {
		return property != null;
	}

	public boolean onlyLiterals() {
		var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return factory.getLattice().getEvaluatedPropertyAnnotation(
				factory.getQualifierHierarchy().findAnnotationInHierarchy(annotations, factory.getTop())) != null;
	}

}
