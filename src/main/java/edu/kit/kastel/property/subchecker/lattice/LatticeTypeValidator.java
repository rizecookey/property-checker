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

import com.sun.source.tree.Tree;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeValidator;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedArrayType;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.type.DeclaredType;
import javax.lang.model.type.TypeMirror;

public final class LatticeTypeValidator extends BaseTypeValidator {

    public LatticeTypeValidator(
            BaseTypeChecker checker,
            BaseTypeVisitor<?> visitor,
            AnnotatedTypeFactory atypeFactory) {
        super(checker, visitor, atypeFactory);
    }

    @Override
    public boolean isValid(AnnotatedTypeMirror type, Tree tree) {
        LatticeAnnotatedTypeFactory factory = getPropertyAnnotatedTypeFactory();
        AnnotationMirror annotation = type.getEffectiveAnnotationInHierarchy(factory.getTop());
        
        EvaluatedPropertyAnnotation epa = factory.getLattice()
                .getEvaluatedPropertyAnnotation(annotation);

        if (type instanceof AnnotatedArrayType) {
            // TODO Annotations on arrays are not supported.
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

        TypeMirror expectedSubjectType = epa.getAnnotationType().getSubjectType();
        TypeMirror actualSubjectType = type.getUnderlyingType();

        if (expectedSubjectType == null) {
            // any
            return true;
        }

        if (expectedSubjectType instanceof DeclaredType decl && TypesUtils.getQualifiedName(decl).equals("java.lang.Object")
                && !TypesUtils.isPrimitive(type.getUnderlyingType())) {
            return true;
        }

        if (actualSubjectType != null && expectedSubjectType != null
                && !checker.getTypeUtils().isAssignable(actualSubjectType, expectedSubjectType)) {
            reportInvalidType(type, tree);
            return false;
        }

        return true;
    }

    public boolean dependsOnlyOnAbstractState(AnnotatedTypeMirror type, AnnotatedTypeMirror exclType, Tree tree) {
        LatticeAnnotatedTypeFactory factory = getPropertyAnnotatedTypeFactory();
        ExclusivityAnnotatedTypeFactory exclFactory = getLatticeSubchecker().getExclusivityFactory();
        AnnotationMirror annotation = type.getEffectiveAnnotationInHierarchy(factory.getTop());
        AnnotationMirror exclAnnotation = exclType.getEffectiveAnnotationInHierarchy(exclFactory.READ_ONLY);
        
        PropertyAnnotation pa = factory.getLattice().getPropertyAnnotation(annotation);
        
        if (!pa.getAnnotationType().isTrivial()
                && (exclAnnotation == null || AnnotationUtils.areSame(exclAnnotation, exclFactory.READ_ONLY))) {
            return false;
        }

        //TODO Abstract state!
        
        return true;
    }

    @Override
    public boolean areBoundsValid(AnnotatedTypeMirror upperBound, AnnotatedTypeMirror lowerBound) {
        // TODO Generics are not supported.
        return true;
    }

    public LatticeAnnotatedTypeFactory getPropertyAnnotatedTypeFactory() {
        return (LatticeAnnotatedTypeFactory) atypeFactory;
    }

    public LatticeSubchecker getLatticeSubchecker() {
        return (LatticeSubchecker) checker;
    }
}
