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

import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.util.ClassUtils;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.type.TypeMirror;
import java.lang.annotation.Annotation;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

public final class PropertyAnnotationType {

    private Class<? extends Annotation> annotationType;
    private TypeMirror annotatedType;
    private List<Parameter> parameters;
    private String wfCondition;
    private String property;

    private Method wfMethod;
    private Method propertyMethod;

    public PropertyAnnotationType(
            Class<? extends Annotation> annotationType,
            TypeMirror annotatedType,
            List<Parameter> parameters,
            String property,
            String precondition) {
        this.annotationType = annotationType;
        this.annotatedType = annotatedType;
        this.parameters = parameters;
        this.property = property;
        this.wfCondition = precondition;
    }

    @SuppressWarnings("nls")
    @Override
    public String toString() {
        return String.format(
                "@%s(%s) %s <==> %s for %s",
                annotationType.getSimpleName(),
                parameters.stream().map(Parameter::toString).collect(Collectors.joining(", ")),
                annotatedType == null ? "any" : TypesUtils.simpleTypeName(annotatedType),
                property,
                wfCondition);
    }

    @Override
    public int hashCode() {
        return Objects.hash(
                annotatedType == null ? 0 : ClassUtils.getCanonicalName(annotatedType),
                annotationType.getName(),
                parameters,
                wfCondition,
                property);
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (!(obj instanceof PropertyAnnotationType)) {
            return false;
        }
        PropertyAnnotationType other = (PropertyAnnotationType) obj;
        return Objects.equals(ClassUtils.getCanonicalName(annotatedType), ClassUtils.getCanonicalName(other.annotatedType))
                && Objects.equals(annotationType.getName(), other.annotationType.getName())
                && Objects.equals(parameters, other.parameters)
                && Objects.equals(wfCondition, other.wfCondition)
                && Objects.equals(property, other.property);
    }

    public String getWFCondition() {
        return wfCondition;
    }

    public String getProperty() {
        return property;
    }

    public Class<? extends Annotation> toClass() {
        return annotationType;
    }

    public String getName() {
        return annotationType.getSimpleName();
    }

    public TypeMirror getSubjectType() {
        return annotatedType;
    }

    public Method getWFMethod() {
        return wfMethod;
    }

    public void setWFMethod(Method wfMethod) {
        this.wfMethod = wfMethod;
    }

    public Method getPropertyMethod() {
        return propertyMethod;
    }

    public void setPropertyMethod(Method propertyMethod) {
        this.propertyMethod = propertyMethod;
    }

    public List<Parameter> getParameters() {
        return Collections.unmodifiableList(parameters);
    }

    public WellFormednessCheckable getWellFormednessCheckable() {
        return new WellFormednessCheckable();
    }

    public PropertyCheckable getPropertyCheckable() {
        return new PropertyCheckable();
    }

    @SuppressWarnings("nls")
    public boolean isTrivial() {
        return getProperty().equals("true") && getWFCondition().equals("true");
    }

    public boolean isBottom(LatticeAnnotatedTypeFactory factory) {
        return annotationType.getSimpleName().equals(
                factory.getBottom().getAnnotationType().asElement().getSimpleName().toString());
    }

    // Used by LatticeVisitor to determine whether to suppress every error if this qualifier
    // appears on a constructor, since a constructor result is never null
    public boolean isNonNull() {
        return getWFCondition().equals("true") && getProperty().equals("§subject§ != null");
    }

    // Used by JavaJMLPrinter to avoid adding `\invariant_for(this)` where it is implicitly added by the JML semantics
    public boolean isInv() {
        return getWFCondition().equals("true") && getProperty().equals("§subject§ != null ==> \\invariant_for(§subject§)");
    }

    @SuppressWarnings("nls")
    public static enum ParameterType {
        CHAR("char", char.class),
        BYTE("byte", byte.class),
        INT("int", int.class),
        SHORT("short", short.class),
        LONG("long", long.class),
        FLOAT("float", float.class),
        DOUBLE("double", double.class),
        BOOLEAN("boolean", boolean.class),
        STRING("String", String.class);

        private String str;
        private Class<?> cls;
        private Method fromStringMethod;

        private ParameterType(String str, Class<?> cls) {
            this.str = str;
            this.cls = cls;

            try {
                switch(str) {
                case "int":
                    this.fromStringMethod = Integer.class.getMethod("parseInt", String.class);
                    break;
                case "short":
                    this.fromStringMethod = Short.class.getMethod("parseShort", String.class);
                    break;
                case "long":
                    this.fromStringMethod = Long.class.getMethod("parseLong", String.class);
                    break;
                case "float":
                    this.fromStringMethod = Float.class.getMethod("parseFloat", String.class);
                    break;
                case "double":
                    this.fromStringMethod = Double.class.getMethod("parseDouble", String.class);
                    break;
                case "boolean":
                    this.fromStringMethod = Boolean.class.getMethod("parseBoolean", String.class);
                    break;
                case "String":
                    this.fromStringMethod = String.class.getMethod("valueOf", Object.class);
                    break;
                }
            } catch (NoSuchMethodException | SecurityException e) {
                throw new AssertionError();
            }
        }
        @Override
        public String toString() {
            return str;
        }

        public Class<?> toClass() {
            return cls;
        }

        public Object fromString(String str) {
            try {
                return fromStringMethod.invoke(null, str);
            } catch (IllegalAccessException
                    | IllegalArgumentException
                    | InvocationTargetException e) {
                throw new IllegalArgumentException();
            }
        }
    }

    public static class Parameter {

        private ParameterType type;
        private String name;

        public Parameter(ParameterType type, String name) {
            this.type = type;
            this.name = name;
        }

        @SuppressWarnings("nls")
        @Override
        public String toString() {
            return type.name().toLowerCase() + " " + name;
        }

        public String getName() {
            return name;
        }

        public ParameterType getType() {
            return type;
        }

        public void setValue(AnnotationBuilder builder, Object value) {
            builder.setValue(name, value.toString());
        }
    }

    public class WellFormednessCheckable implements Checkable {

        private WellFormednessCheckable() { }

        @Override
        public Method getCheckerMethod() {
            return PropertyAnnotationType.this.getWFMethod();
        }

        @Override
        public void setCheckerMethod(Method checkerMethod) {
            PropertyAnnotationType.this.setWFMethod(checkerMethod);
        }

        @Override
        public String getCondition() {
            return PropertyAnnotationType.this.getWFCondition();
        }

        @Override
        public String[] getParameterNames() {
            return PropertyAnnotationType.this.parameters.stream()
                    .map(Parameter::getName).toArray(String[]::new);
        }

        @Override
        public Class<?>[] getParameterTypes() {
            return PropertyAnnotationType.this.parameters.stream()
                    .map(Parameter::getType).map(ParameterType::toClass).toArray(Class<?>[]::new);
        }

        @Override
        public String toString() {
            return PropertyAnnotationType.this.toString();
        }

        public PropertyAnnotationType getPropertyAnnotationType() {
            return PropertyAnnotationType.this;
        }
    }

    public class PropertyCheckable implements Checkable {

        private PropertyCheckable() { }

        @Override
        public Method getCheckerMethod() {
            return PropertyAnnotationType.this.getPropertyMethod();
        }

        @Override
        public void setCheckerMethod(Method checkerMethod) {
            PropertyAnnotationType.this.setPropertyMethod(checkerMethod);
        }

        @Override
        public String getCondition() {
            return PropertyAnnotationType.this.getProperty();
        }

        @Override
        public String[] getParameterNames() {
            List<String> result = new ArrayList<>();
            result.add(Config.SUBJECT_NAME);
            result.addAll(PropertyAnnotationType.this.parameters.stream()
                    .map(Parameter::getName).collect(Collectors.toList()));
            return result.toArray(new String[0]);
        }

        @Override
        public Class<?>[] getParameterTypes() {
            List<Class<?>> result = new ArrayList<>();
            result.add(annotatedType == null ? null : TypesUtils.getClassFromType(annotatedType));
            result.addAll(PropertyAnnotationType.this.parameters.stream()
                    .map(Parameter::getType).map(ParameterType::toClass).collect(Collectors.toList()));
            return result.toArray(new Class<?>[0]);
        }

        @Override
        public String toString() {
            return PropertyAnnotationType.this.toString();
        }

        public PropertyAnnotationType getPropertyAnnotationType() {
            return PropertyAnnotationType.this;
        }
    }
}
