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

import com.sun.source.tree.*;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.packing.PackingVisitor;
import edu.kit.kastel.property.printer.JavaJMLPrinter;
import edu.kit.kastel.property.printer.PrettyPrinter;
import edu.kit.kastel.property.smt.SmtCompiler;
import edu.kit.kastel.property.smt.SmtExpression;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.FileUtils;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;
import org.sosy_lab.java_smt.api.SolverException;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Paths;
import java.util.*;

public final class PropertyVisitor extends PackingVisitor {

    private TreePath path;

    Map<MethodTree, AnnotationMirror[]> inputPackingTypes = new HashMap<>();
    Map<MethodTree, AnnotationMirror[]> outputPackingTypes = new HashMap<>();

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
            mendTypeErrors(results);
            // TODO: fix reporting here (results is never empty, even if there are no proof obligations left)
            if (results.isEmpty()) {
                PrettyPrinter printer = new PrettyPrinter(out, true);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with no remaining proof obligations",
                        checker.getRelativeSourceFileName()));
            } else {
                JavaJMLPrinter printer = new JavaJMLPrinter(results, checker, out);
                printer.printUnit((JCTree.JCCompilationUnit) checker.getVisitor().getPath().getCompilationUnit(), null);
                System.out.println(String.format(
                        "Wrote file %s with: \n\t%d assertions (to be proven in JML)\n\t%d assumptions (proven by checker)\n\t%d non-free method preconditions (to be proven in JML)\n\t%d free method preconditions (proven by checker)\n\t%d non-free method postconditions (to be proven in JML)\n\t%d free method postconditions (proven by checker)",
                        checker.getRelativeSourceFileName(),
                        printer.getAssertions(), printer.getAssumptions(),
                        printer.getMethodCallPreconditions(), printer.getFreeMethodCallPreconditions(),
                        printer.getMethodCallPostconditions(), printer.getFreeMethodCallPostconditions()));
                // LatticeVisitors are reused, but result contents are compilation-unit-specific, so we reset them
                results.forEach(LatticeVisitor.Result::clear);
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    private void mendTypeErrors(List<LatticeVisitor.Result> results) {
        System.out.println();
        System.out.println("File: " + root.getSourceFile().getName());
        // merge contexts from all lattices
        Map<Tree, Set<SmtExpression>> contexts = new HashMap<>();
        for (LatticeVisitor.Result result : results) {
            result.getContexts()
                    .forEach((tree, context) -> contexts.computeIfAbsent(tree, v -> new HashSet<>()).addAll(context));
        }

        try (var solverContext = SolverContextFactory.createSolverContext(SolverContextFactory.Solvers.SMTINTERPOL)) {
            // go through all expression trees that caused type errors
            results.stream()
                    .map(LatticeVisitor.Result::getMendingConditions)
                    .map(Map::keySet)
                    .flatMap(Set::stream)
                    .distinct()
                    .forEach(tree -> processMendableExpression(solverContext, results, contexts.getOrDefault(tree, Set.of()), tree));
            // go through all packing calls with uninitialized fields left
            results.stream()
                    .map(LatticeVisitor.Result::getUninitializedFields)
                    .map(Map::keySet)
                    .flatMap(Set::stream)
                    .distinct()
                    .forEach(tree -> processMendablePackingCall(solverContext, results, contexts.getOrDefault(tree, Set.of()), tree));
        } catch (InvalidConfigurationException e) {
            throw new RuntimeException(e);
        }
    }

    private void processMendableExpression(
            SolverContext solverContext,
            List<LatticeVisitor.Result> results,
            Set<SmtExpression> context,
            Tree expression
    ) {
        SmtCompiler compiler = new SmtCompiler(solverContext);
        var conjunction = contextConjunction(compiler, expression, context);
        for (LatticeVisitor.Result result : results) {
            var condition = result.getMendingConditions().get(expression);
            if (condition == null) {
                continue;
            }
            if (universallyValid(solverContext, compiler, conjunction, condition)) {
                result.removeTypeError(TreePath.getPath(checker.getPathToCompilationUnit(), expression));
            }
        }
    }

    private void processMendablePackingCall(
            SolverContext solverContext,
            List<LatticeVisitor.Result> results,
            Set<SmtExpression> context,
            Tree packingCall
    ) {
        SmtCompiler compiler = new SmtCompiler(solverContext);
        var conjunction = contextConjunction(compiler, packingCall, context);
        for (LatticeVisitor.Result result : results) {
            var fields = result.getUninitializedFields().getOrDefault(packingCall, Collections.emptyList()).iterator();
            while (fields.hasNext()) {
                var condition = result.getFieldRefinement(fields.next());
                if (universallyValid(solverContext, compiler, conjunction, condition)) {
                    fields.remove();
                }
            }
        }
    }

    private Deque<BooleanFormula> contextConjunction(SmtCompiler compiler, Tree tree, Set<SmtExpression> context) {
        var lineMap = root.getLineMap();
        var pos = trees.getSourcePositions().getStartPosition(root, tree);
        System.out.printf("=== Mending type errors for expression %s (%d:%d) using combined context:%n",
                tree, lineMap.getLineNumber(pos), lineMap.getColumnNumber(pos));
        Deque<BooleanFormula> conjunction = new ArrayDeque<>();

        // add context formulae
        for (SmtExpression expr : context) {
            try {
                conjunction.push((BooleanFormula) compiler.compile(expr));
                System.out.println(expr);
            } catch (UnsupportedOperationException e) {
                // drop context constraints that aren't representable
                System.out.printf("(Ignoring context formula %s due to use of unsupported feature: %s%n)",
                        expr, e.getMessage());
            }
        }
        System.out.println("== Proof attempts");
        return conjunction;
    }

    private boolean universallyValid(SolverContext solverContext, SmtCompiler compiler, Deque<BooleanFormula> contextConjunction, SmtExpression condition) {
        BooleanFormulaManager bmgr = solverContext.getFormulaManager().getBooleanFormulaManager();

        // add proof goal to conjunction
        try {
            contextConjunction.push(bmgr.not((BooleanFormula) compiler.compile(condition)));
        } catch (UnsupportedOperationException e) {
            System.out.printf("(Skipping proof goal %s due to use of unsupported feature: %s%n)",
                    condition, e.getMessage());
            return false;
        }

        System.out.printf("Proof goal: %s", condition);
        try (var proverEnv = solverContext.newProverEnvironment()) {
            proverEnv.addConstraint(bmgr.and(contextConjunction));
            var assignmentValid = proverEnv.isUnsat();
            System.out.println(assignmentValid ? " (success)" : " (failed)");
            return assignmentValid;
        } catch (InterruptedException | SolverException e) {
            System.out.println("Encountered exception while trying to prove goal " + condition);
            e.printStackTrace();
        } finally {
            // context formulae stay in the conjunction, we only remove the proof goal (which was added last)
            contextConjunction.pop();
        }
        return false;
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
    protected void checkFieldsInitializedUpToFrame(
            Tree tree,
            TypeMirror frame) {
        for (BaseTypeChecker targetChecker : getChecker().getTargetCheckers()) {
            GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory = targetChecker.getTypeFactory();

            List<VariableElement> uninitializedFields =
                    atypeFactory.getUninitializedFields(
                            atypeFactory.getStoreBefore(tree),
                            targetFactory.getStoreBefore(tree),
                            getCurrentPath(),
                            false,
                            List.of());

            // Remove fields below frame
            uninitializedFields.retainAll(ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), elements));

            // Remove fields with a relevant @SuppressWarnings annotation
            uninitializedFields.removeIf(
                    f -> checker.shouldSuppressWarnings(f, "initialization.field.uninitialized"));

            if (!uninitializedFields.isEmpty()) {
                StringJoiner fieldsString = new StringJoiner(", ");
                for (VariableElement f : uninitializedFields) {
                    fieldsString.add(f.getSimpleName());
                }
                checker.reportError(tree, "initialization.fields.uninitialized", fieldsString);

                // Add uninitialized fields to LatticeVisitor for JML printer to use
                if (targetChecker instanceof LatticeSubchecker) {
                    LatticeVisitor latticeVisitor = (LatticeVisitor) targetChecker.getVisitor();
                    latticeVisitor.addUninitializedFields(tree, uninitializedFields);
                }
            }
        }
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        return super.visitAssignment(node, p);
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        return new PropertyAnnotatedTypeFactory(checker);
    }

    public PropertyChecker getPropertyChecker() {
        return (PropertyChecker) checker;
    }
}
