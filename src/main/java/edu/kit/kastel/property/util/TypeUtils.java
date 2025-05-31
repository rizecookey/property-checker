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

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import org.checkerframework.dataflow.cfg.node.ArrayCreationNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import java.util.ArrayList;
import java.util.List;

public final class TypeUtils {

    private TypeUtils() { }

    public static int getParameterIndex(MethodTree tree, JavaExpression param) {
        int i = 0;
        for (; i < tree.getParameters().size(); ++i) {
            if (TreeUtils.elementFromDeclaration(tree.getParameters().get(i)).equals(param)) {
                break;
            }
        }

        if (ElementUtils.isStatic(TreeUtils.elementFromDeclaration(tree))) {
            return i;
        } else {
            return param.toString().equals("this") ? 0 : i + 1;
        }
    }

    public static int getParameterIndex(MethodTree tree, VariableTree param) {
        int i = 0;
        for (; i < tree.getParameters().size(); ++i) {
            if (tree.getParameters().get(i).equals(param)) {
                break;
            }
        }

        return param.equals(tree.getReceiverParameter()) ? 0 : i + 1;
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

    /**
     * Determines whether the expression's value can be stored in a {@link org.checkerframework.framework.flow.CFAbstractStore}.
     *
     * @param expr an expression.
     * @return whether the expression's value can be stored in a store.
     */
    public static boolean isStoreExpression(JavaExpression expr) {
        return expr instanceof LocalVariable
            || expr instanceof ThisReference
            || expr instanceof FieldAccess
            || expr instanceof MethodCall
            || expr instanceof ArrayAccess
            || expr instanceof ClassName;
    }

    public static Node getArgumentWithVarargs(MethodInvocationNode node, int i) {
        int num = node.getArguments().size();
        if (i >= num - 1 && node.getArgument(num - 1) instanceof ArrayCreationNode arrayCreationNode && arrayCreationNode.getInitializers().size() > 0) {
            return arrayCreationNode.getInitializer(i - num + 1);
        } else {
            return node.getArgument(i);
        }
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
