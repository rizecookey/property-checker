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
package edu.kit.kastel.property.util;

import com.sun.source.tree.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;
import org.checkerframework.javacutil.TreeUtils;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

public final class TypeUtils {

    private TypeUtils() { }

    public static int getParameterIndex(MethodTree tree, JavaExpression param) {
        if (param instanceof LocalVariable localParam) {
            for (int i = 0; i < tree.getParameters().size(); ++i) {
                if (TreeUtils.elementFromDeclaration(tree.getParameters().get(i)).equals(localParam.getElement())) {
                    return i + 1;
                }
            }
            throw new AssertionError();
        } else if (param instanceof ThisReference) {
            return 0;
        } else {
            throw new UnsupportedOperationException(
                    String.format("Postcondition types on non-parameters are not supported (method: %s, subject: %s)",
                            tree.getName(), param));
        }
    }

    public static int getParameterIndex(MethodTree tree, VariableTree param) {
        if (param.equals(tree.getReceiverParameter())) {
            return 0;
        } else {
            for (int i = 0; i < tree.getParameters().size(); ++i) {
                if (tree.getParameters().get(i).equals(param)) {
                    return i + 1;
                }
            }
            throw new AssertionError();
        }
    }

    public static int getArgumentIndex(MethodInvocationTree tree, Tree argument) {
        if (Objects.equals(tree.getMethodSelect(), argument)) {
            return 0;
        }
        for (int i = 0; i < tree.getArguments().size(); i++) {
            if (tree.getArguments().get(i).equals(argument)) {
                return i + 1;
            }
        }
        return -1;
    }

    public static int getArgumentIndex(NewClassTree tree, Tree argument) {
        for (int i = 0; i < tree.getArguments().size(); i++) {
            if (tree.getArguments().get(i).equals(argument)) {
                return i;
            }
        }
        return -1;
    }

    public static String unannotatedTypeName(AnnotatedTypeMirror mirror) {
        if (mirror instanceof AnnotatedExecutableType) {
            throw new IllegalArgumentException();
        }

        if (mirror.getUnderlyingType() instanceof ArrayType) {
            return ((ArrayType) mirror.getUnderlyingType()).elemtype.asElement().toString() + "[]";
        } else {
            return ((Type) mirror.getUnderlyingType()).asElement().toString();
        }
    }

    public static boolean sameTree(Tree tree0, Tree tree1) {
        return tree0.getKind() == tree1.getKind() && tree0.toString().equals(tree1.toString());
    }

    /**
     * Returns a list of all fields of the given class and its superclasses.
     *
     * @param clazz the class
     * @return a list of all fields of {@code clazz} and superclasses
     */
    public static List<VariableTree> allFieldsInHierarchy(ClassTree clazz) {
        List<VariableTree> fields = new ArrayList<>();
        allFieldsInHierarchy(clazz, fields);
        return fields;
    }

    private static void allFieldsInHierarchy(ClassTree clazz, List<VariableTree> fields) {
        for (Tree t : clazz.getMembers()) {
            if (t.getKind() == Tree.Kind.VARIABLE) {
                VariableTree vt = (VariableTree) t;
                fields.add(vt);
            }
        }

        Tree superType = clazz.getExtendsClause();
        if (superType instanceof ClassTree) {
            allFieldsInHierarchy((ClassTree) clazz.getExtendsClause());
        }
    }
}
