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

import com.google.common.collect.Streams;
import com.sun.source.util.TreePath;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.lattice.PropertyAnnotationType.Parameter;
import edu.kit.kastel.property.lattice.compiler.ClassBuilder;
import org.checkerframework.dataflow.expression.FormalParameter;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.source.SourceChecker;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreePathUtil;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.*;
import java.util.stream.Collectors;

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

    /**
     * Returns the complete, concrete refinement expression (well-formedness condition + property)
     * for this property annotation as Java code. The actual arguments are inserted for the parameter placeholders,
     * and the subject placeholder is substituted by the value given as a parameter to this method.
     *
     * @param subject The subject this property annotation should apply to
     * @return A boolean Java expression in string form.
     */
    public String combinedRefinement(CharSequence subject) {
        String property = annotationType.getProperty()
                .replace("§subject§", "(" + subject + ")");
        String wfCondition = annotationType.getWFCondition()
                .replace("§subject§", "(" + subject + ")");
        var actualParams = actualParameters.iterator();
        for (PropertyAnnotationType.Parameter param : annotationType.getParameters()) {
            String actual = "(" + actualParams.next() + ")";
            String placeholder = "§" + param.getName() + "§";
            wfCondition = wfCondition.replace(placeholder, actual);
            property = property.replace(placeholder, actual);
        }
        return String.format("(%s) && (%s)", wfCondition, property);
    }

    public JavaExpression parseRefinement(TreePath localVarPath, SourceChecker checker)
            throws JavaExpressionParseUtil.JavaExpressionParseException {
        // for the subject, we use the checker framework's special parameter # syntax.
        String refinement = combinedRefinement("#1");
        var subjectParam = subject(checker.getProcessingEnvironment());

        TypeMirror enclosingType = TreeUtils.elementFromDeclaration(TreePathUtil.enclosingClass(localVarPath)).asType();
        ThisReference thisReference = TreePathUtil.isTreeInStaticScope(localVarPath)
                ? null
                : new ThisReference(enclosingType);
        return JavaExpressionParseUtil.parse(
                    refinement, enclosingType, thisReference,
                    List.of(subjectParam), localVarPath,
                    checker.getPathToCompilationUnit(), checker.getProcessingEnvironment());
    }

    public JavaExpression parseRefinement(VariableElement field, SourceChecker checker)
            throws JavaExpressionParseUtil.JavaExpressionParseException {
        String refinement = combinedRefinement("#1");
        TypeMirror enclosingType = field.getEnclosingElement().asType();
        ThisReference thisReference = ElementUtils.isStatic(field) ? null : new ThisReference(enclosingType);
        return JavaExpressionParseUtil.parse(refinement, enclosingType, thisReference,
                List.of(subject(checker.getProcessingEnvironment())), null,
                checker.getPathToCompilationUnit(), checker.getProcessingEnvironment());
    }

    private FormalParameter subject(ProcessingEnvironment env) {
        return new FormalParameter(1, new SubjectVariableElement(
                Objects.requireNonNullElse(
                        getAnnotationType().getSubjectType(),
                        TypesUtils.getObjectTypeMirror(env))
        ));
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

                if (cls == null) {
                    return null;
                }

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
