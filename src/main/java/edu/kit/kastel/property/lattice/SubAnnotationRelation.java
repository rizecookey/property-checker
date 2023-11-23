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
package edu.kit.kastel.property.lattice;

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.stream.Stream;

import edu.kit.kastel.property.lattice.PropertyAnnotationType.Parameter;
import edu.kit.kastel.property.lattice.PropertyAnnotationType.ParameterType;

public class SubAnnotationRelation implements Checkable {

    private PropertyAnnotation subAnnotation;
    private PropertyAnnotation superAnnotation;

    private String condition;

    private Method checkerMethod;

    public SubAnnotationRelation(
            PropertyAnnotation subAnnotation,
            PropertyAnnotation superAnnotation,
            String condition) {
        this.subAnnotation = subAnnotation;
        this.superAnnotation = superAnnotation;
        this.condition = condition;
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return subAnnotation + " :< " + superAnnotation + " <==> " + condition;
    }

    @Override
    public int hashCode() {
        return Objects.hash(condition, subAnnotation, superAnnotation);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof SubAnnotationRelation)) {
            return false;
        }
        SubAnnotationRelation other = (SubAnnotationRelation) obj;
        return Objects.equals(condition, other.condition)
                && Objects.equals(subAnnotation, other.subAnnotation)
                && Objects.equals(superAnnotation, other.superAnnotation);
    }

    @Override
    public String[] getParameterNames() {
        return Stream.concat(
                getSubAnnotation().getActualParameters().stream(),
                getSuperAnnotation().getActualParameters().stream()).toArray(String[]::new);
    }

    @Override
    public Class<?>[] getParameterTypes() {
        return Stream.concat(
                getSubAnnotation().getAnnotationType().getParameters().stream(),
                getSuperAnnotation().getAnnotationType().getParameters().stream())
        .map(Parameter::getType).map(ParameterType::toClass).toArray(Class<?>[]::new);
    }

    public void setCheckerMethod(Method checkerMethod) {
        this.checkerMethod = checkerMethod;
    }

    public Method getCheckerMethod() {
        return checkerMethod;
    }

    public PropertyAnnotation getSubAnnotation() {
        return subAnnotation;
    }

    public PropertyAnnotation getSuperAnnotation() {
        return superAnnotation;
    }

    public String getSubAnnotationName() {
        return subAnnotation.getAnnotationType().getName();
    }

    public String getSuperAnnotationName() {
        return superAnnotation.getAnnotationType().getName();
    }

    public String getCondition() {
        return condition;
    }

    public boolean checkCondition(
            EvaluatedPropertyAnnotation subAnnotation,
            EvaluatedPropertyAnnotation superAnnotation) {
        return checkCondition(subAnnotation.getActualParameters(), superAnnotation.getActualParameters());
    }

    public boolean checkCondition(
            List<Object> subAnnotationActualParams,
            List<Object> superAnnotationActualParams) {
        if (checkerMethod == null) {
            throw new IllegalStateException();
        }


        List<Object> actualParams = new ArrayList<>(subAnnotationActualParams);
        actualParams.addAll(superAnnotationActualParams);

        try {
            return (Boolean) getCheckerMethod().invoke(null, actualParams.toArray());
        } catch (IllegalAccessException | InvocationTargetException e) {
            throw new AssertionError();
        }
    }
}
