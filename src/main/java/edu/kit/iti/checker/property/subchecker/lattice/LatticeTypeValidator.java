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
package edu.kit.iti.checker.property.subchecker.lattice;

import javax.lang.model.element.AnnotationMirror;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeValidator;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedArrayType;
import org.checkerframework.javacutil.AnnotationUtils;

import com.sun.source.tree.Tree;
import com.sun.tools.javac.code.Type;

import edu.kit.iti.checker.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.iti.checker.property.util.ClassUtils;

public class LatticeTypeValidator extends BaseTypeValidator {

    public LatticeTypeValidator(
            BaseTypeChecker checker,
            BaseTypeVisitor<?> visitor,
            AnnotatedTypeFactory atypeFactory) {
        super(checker, visitor, atypeFactory);
    }

    @Override
    public boolean isValid(AnnotatedTypeMirror type, Tree tree) {
        LatticeAnnotatedTypeFactory factory = getPropertyAnnotatedTypeFactory();
        AnnotationMirror annotation = type.getAnnotationInHierarchy(factory.getTop());

        EvaluatedPropertyAnnotation epa = factory.getLattice()
                .getEvaluatedPropertyAnnotation(annotation);

        if (type instanceof AnnotatedArrayType) {
            // Annotations on arrays are not supported.
            // Just return true to prevent any error messages.
            return true;
        }

        if (epa == null) {
            // TODO implement validity checks for non-literal arguments.
            return true;
        }

        if (!super.isValid(type, tree)) {
            return false;
        }

        if (!epa.checkWFCondition()) {
            reportInvalidType(type, tree);
            return false;
        }

        if (AnnotationUtils.areSame(annotation, factory.getTop())) {
            return true;
        }

        Class<?> expectedSubjectType = epa.getAnnotationType().getSubjectType();
        Class<?> actualSubjectType = ClassUtils.classOrPrimitiveForName(((Type) type.getUnderlyingType()).asElement().toString(), getPropertyChecker());

        if (actualSubjectType != null && expectedSubjectType != null && !expectedSubjectType.isAssignableFrom(actualSubjectType)) {
            reportInvalidType(type, tree);
            return false;
        }

        return true;
    }

    @Override
    public boolean areBoundsValid(AnnotatedTypeMirror upperBound, AnnotatedTypeMirror lowerBound) {
        // Generics are not supported.
        return true;
    }

    public LatticeAnnotatedTypeFactory getPropertyAnnotatedTypeFactory() {
        return (LatticeAnnotatedTypeFactory) atypeFactory;
    }

    public LatticeSubchecker getPropertyChecker() {
        return (LatticeSubchecker) checker;
    }
}
