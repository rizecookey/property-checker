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
package edu.kit.iti.checker.property.lattice;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import javax.lang.model.element.AnnotationMirror;

import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.Pair;

import edu.kit.iti.checker.property.lattice.PropertyAnnotationType.Parameter;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.iti.checker.property.util.UnorderedPair;

public class Lattice {

    private String ident;

    private LatticeAnnotatedTypeFactory factory;

    private Map<String, PropertyAnnotationType> annotationTypes;
    private Map<Pair<String, String>, SubAnnotationRelation> relations;
    private Map<UnorderedPair<String>, List<Bound>> meets;
    private Map<UnorderedPair<String>, List<Bound>> joins;

    public Lattice(
            LatticeAnnotatedTypeFactory factory,
            String ident,
            Map<String, PropertyAnnotationType> annotationTypes,
            Map<Pair<String, String>, SubAnnotationRelation> relations,
            Map<UnorderedPair<String>, List<Bound>> meets,
            Map<UnorderedPair<String>, List<Bound>> joins) {
        this.factory = factory;

        this.ident = ident;
        this.annotationTypes = annotationTypes;
        this.relations = relations;
        this.meets = meets;
        this.joins = joins;
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return String.format("%s:\n\t%s\n\t%s\n\t%s\n\t%s", ident, annotationTypes.values(), relations.values(), meets, joins);
    }

    public String getIdent() {
        return ident;
    }

    public Map<String, PropertyAnnotationType> getAnnotationTypes() {
        return Collections.unmodifiableMap(annotationTypes);
    }

    public Map<Pair<String, String>, SubAnnotationRelation> getRelations() {
        return Collections.unmodifiableMap(relations);
    }

    public Map<UnorderedPair<String>, List<Bound>> getJoins() {
        return Collections.unmodifiableMap(joins);
    }

    public Map<UnorderedPair<String>, List<Bound>> getMeets() {
        return Collections.unmodifiableMap(meets);
    }


    public PropertyAnnotation getPropertyAnnotation(AnnotatedTypeMirror mirror) {
        return getPropertyAnnotation(mirror.getAnnotationInHierarchy(factory.getTop()));
    }

    public PropertyAnnotation getPropertyAnnotation(AnnotationMirror mirror) {
        PropertyAnnotationType type = annotationTypes.get(
                mirror.getAnnotationType().asElement().getSimpleName().toString());

        List<String> actualParams = new ArrayList<>();
        for (Parameter param : type.getParameters()) {
            String paramStr = AnnotationUtils.getElementValue(mirror, param.getName(), String.class, true);
            actualParams.add(paramStr);
        }

        return new PropertyAnnotation(type, actualParams);
    }

    public EvaluatedPropertyAnnotation getEvaluatedPropertyAnnotation(AnnotatedTypeMirror mirror) {
        return getEvaluatedPropertyAnnotation(mirror.getAnnotationInHierarchy(factory.getTop()));
    }

    public EvaluatedPropertyAnnotation getEvaluatedPropertyAnnotation(AnnotationMirror mirror) {
        PropertyAnnotationType type = annotationTypes.get(
                mirror.getAnnotationType().asElement().getSimpleName().toString());

        try {
            List<Object> actualParams = new ArrayList<>();
            for (Parameter param : type.getParameters()) {
                String paramStr = AnnotationUtils.getElementValue(mirror, param.getName(), String.class, true);
                actualParams.add(param.getType().fromString(paramStr));
            }

            return new EvaluatedPropertyAnnotation(type, actualParams);
        } catch(IllegalArgumentException e) {
            // If fromString throws an IllegalArgumentException, the parameter is not a literal, but
            // a composite expression.
            // The Checker type system always delegates expression of such types to KeY.
            return null;
        }
    }
}
