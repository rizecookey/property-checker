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

import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

import com.google.common.collect.Streams;

import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType.Parameter;
import edu.kit.iti.checker.property.lattice.compiler.ClassBuilder;

public class PropertyAnnotation {

    private PropertyAnnotationType annotationType;
    private List<String> actualParameters;

    private EvaluatedPropertyAnnotation evaluation;

    public PropertyAnnotation(
            PropertyAnnotationType annotationType,
            List<String> actualParameters) {
        this.annotationType = annotationType;
        this.actualParameters = actualParameters;
    }

    public PropertyAnnotationType getAnnotationType() {
        return annotationType;
    }

    public List<String> getActualParameters() {
        return Collections.unmodifiableList(actualParameters);
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return annotationType.getName() + "(" + actualParameters.stream().collect(Collectors.joining(", ")) + ")";
    }

    @Override
    public int hashCode() {
        return Objects.hash(actualParameters, annotationType);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof PropertyAnnotation)) {
            return false;
        }
        PropertyAnnotation other = (PropertyAnnotation) obj;
        return Objects.equals(actualParameters, other.actualParameters)
                && Objects.equals(annotationType, other.annotationType);
    }

    public String getName() {
        return getAnnotationType().getName();
    }

    @SuppressWarnings("nls")
    public EvaluatedPropertyAnnotation evaluate(
            PropertyChecker checker,
            LinkedHashMap<String, Class<?>> evaluationTypeContext,
            LinkedHashMap<String, Object> evaluationValueContext) {
        if (evaluation == null) {
            try {
                evaluation = new EvaluatedPropertyAnnotation(
                        annotationType,
                        Streams.zip(
                                annotationType.getParameters().stream().map(Parameter::getType),
                                actualParameters.stream(),
                                (t, p) -> t.fromString(p)).collect(Collectors.toList()));
            } catch (IllegalArgumentException e) {
                ClassBuilder compiler = new ClassBuilder("Temp"); //$NON-NLS-1$

                for (int i = 0; i < actualParameters.size(); ++i) {
                    compiler.addMethod(
                            "int",
                            "arg" + i,
                            actualParameters.get(i),
                            evaluationTypeContext.values().stream().map(Object::toString).toArray(String[]::new),
                            evaluationValueContext.keySet().toArray(String[]::new),
                            "");
                }

                Class<?> cls = compiler.compile(checker.getProjectClassLoader());

                List<Object> evaluatedParams = new ArrayList<>();

                for (int i = 0; i < actualParameters.size(); ++i) {
                    Method m;
                    try {
                        m = cls.getMethod("arg" + i, evaluationTypeContext.values().toArray(Class<?>[]::new));
                        evaluatedParams.add(m.invoke(null, evaluationValueContext.values().toArray()));
                    } catch (NoSuchMethodException
                            | SecurityException
                            | IllegalAccessException
                            | IllegalArgumentException
                            | InvocationTargetException e1) {
                        throw new AssertionError();
                    }
                }

                evaluation = new EvaluatedPropertyAnnotation(
                        annotationType,
                        evaluatedParams);
            }
        }

        return evaluation;
    }
}
