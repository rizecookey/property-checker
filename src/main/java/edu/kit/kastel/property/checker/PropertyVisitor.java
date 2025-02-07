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
package edu.kit.kastel.property.checker;

import com.sun.source.tree.CompilationUnitTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.packing.PackingVisitor;
import edu.kit.kastel.property.printer.JavaJMLPrinter;
import edu.kit.kastel.property.printer.PrettyPrinter;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.FileUtils;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

public final class PropertyVisitor extends PackingVisitor {

    private TreePath path;

    Map<MethodTree, AnnotationMirror[]> inputPackingTypes = new HashMap<>();
    Map<MethodTree, AnnotationMirror[]> outputPackingTypes = new HashMap<>();

    Map<Tree, TypeMirror> inferredUnpackStatements = new HashMap<>();
    Map<Tree, TypeMirror> inferredPackStatements = new HashMap<>();

    protected PropertyVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    @Override
    public void visit(TreePath path) {
        super.visit(path);
        this.path = path;

        PropertyChecker checker = (PropertyChecker) this.checker;

        File file = Paths.get(checker.getOutputDir(), checker.getRelativeSourceFileName()).toFile();
        file.getParentFile().mkdirs();
        FileUtils.createFile(file);

        try (BufferedWriter out = new BufferedWriter(new FileWriter(file))) {
            List<LatticeVisitor.Result> results = checker.getResults(checker.getAbsoluteSourceFileName());
            if (results.isEmpty()) {
                PrettyPrinter printer = new PrettyPrinter(out, true);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with no remaining proof obligations",
                        checker.getRelativeSourceFileName()));
            } else {
                JavaJMLPrinter printer = new JavaJMLPrinter(checker.getResults(checker.getAbsoluteSourceFileName()), checker, out);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)\n\t%d non-free method postconditions (to be proven in JML)\n\t%d free method postconditions (proven by checker)",
                        checker.getRelativeSourceFileName(),
                        printer.getAssertions(), printer.getAssumptions(),
                        printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions(),
                        printer.getMethodCallPostconditions(), printer.getFreeMethodCallPostconditions()));
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    TreePath getPath() {
        return path;
    }

    CompilationUnitTree getRoot() {
        return root;
    }

    @Override
    public Void visitMethod(MethodTree tree, Void p) {
        inputPackingTypes.put(tree, new AnnotationMirror[tree.getParameters().size() + 1]);
        outputPackingTypes.put(tree, new AnnotationMirror[tree.getParameters().size() + 1]);

        for (int i = 0; i < tree.getParameters().size(); ++i) {
            VariableTree param = tree.getParameters().get(i);
            inputPackingTypes.get(tree)[i + 1] = atypeFactory.getAnnotatedType(param).getAnnotationInHierarchy(atypeFactory.getInitialized());
        }

        if (TreeUtils.isConstructor(tree)) {
            outputPackingTypes.get(tree)[0] = getDeclaredConstructorResult(tree);
        } else if (tree.getReceiverParameter() != null) {
            inputPackingTypes.get(tree)[0] = atypeFactory.getAnnotatedType(tree.getReceiverParameter()).getAnnotationInHierarchy(atypeFactory.getInitialized());
        }
        return super.visitMethod(tree, p);
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        int paramIdx = TypeUtils.getParameterIndex(methodTree, expression);
        outputPackingTypes.get(methodTree)[paramIdx] = annotation;
        super.checkPostcondition(methodTree, annotation, expression);
    }

    @Override
    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingStore exitStore) {
        int paramIdx = TypeUtils.getParameterIndex(methodTree, param);
        outputPackingTypes.get(methodTree)[paramIdx] = atypeFactory.getAnnotatedTypeLhs(param).getAnnotationInHierarchy(atypeFactory.getInitialized());
        super.checkDefaultContract(param, methodTree, exitStore);
    }

    @Override
    protected void reportUninitializedFieldsError(Tree tree, BaseTypeChecker targetChecker, List<VariableElement> uninitializedFields) {
        super.reportUninitializedFieldsError(tree, targetChecker, uninitializedFields);

        // Add uninitialized fields to LatticeVisitor for JML printer to use
        if (targetChecker instanceof LatticeSubchecker) {
            LatticeVisitor latticeVisitor = (LatticeVisitor) targetChecker.getVisitor();
            latticeVisitor.addUninitializedFields(tree, uninitializedFields);
        }
    }

    @Override
    protected void inferPackStatement(Tree tree, TypeMirror frame) {
        this.inferredPackStatements.put(tree, frame);
    }

    @Override
    protected void inferUnpackStatement(Tree tree, TypeMirror frame) {
        this.inferredUnpackStatements.put(tree, frame);
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        return new PropertyAnnotatedTypeFactory(checker);
    }

    public PropertyChecker getPropertyChecker() {
        return (PropertyChecker) checker;
    }
}
