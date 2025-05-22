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

import com.sun.source.tree.*;
import com.sun.source.tree.Tree.Kind;
import com.sun.source.util.SourcePositions;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingClientVisitor;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.util.TypeUtils;
import edu.kit.kastel.property.util.Union;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.Pair;
import org.checkerframework.javacutil.TreeUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.Name;
import javax.lang.model.type.TypeKind;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public final class LatticeVisitor extends PackingClientVisitor<LatticeAnnotatedTypeFactory> implements CooperativeVisitor {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    private CooperativeVisitor.Result result;

    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;

    protected LatticeVisitor(BaseTypeChecker checker, LatticeAnnotatedTypeFactory typeFactory) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());

        result = new CooperativeVisitor.Result(getLatticeSubchecker());
    }

    public LatticeVisitor(BaseTypeChecker checker) {
        this(checker, null);
    }

    @Override
    public void visit(TreePath path) {
        super.visit(path);

        ((PropertyChecker) checker.getParentChecker()).addResult(getAbsoluteSourceFileName(), result);
    }

    @Override
    public Void visitAnnotation(AnnotationTree tree, Void p) {
        // do nothing
        return p;
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        call(() -> super.visitReturn(node, p), () -> result.illTypedMethodResults.add(enclMethod));
        return null;
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        final int paramIdx = TypeUtils.getParameterIndex(methodTree, expression);
        result.methodOutputTypes.get(methodTree)[paramIdx] = annotation;
        call(
                () -> super.checkPostcondition(methodTree, annotation, expression),
                () -> result.addIllTypedMethodOutputParam(methodTree, paramIdx));
    }

    @Override
    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingClientStore<?, ?> exitStore) {
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(((JCTree) param).type);
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }
        final int paramIdx = TypeUtils.getParameterIndex(methodTree, param);
        if (!paramsInContract.contains(paramExpr)) {
            result.methodOutputTypes.get(methodTree)[paramIdx] = atypeFactory.getAnnotatedTypeLhs(param).getEffectiveAnnotationInHierarchy(atypeFactory.getTop());
        }
        call(
                () -> super.checkDefaultContract(param, methodTree, exitStore),
                () -> result.addIllTypedMethodOutputParam(methodTree, paramIdx));
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
        if (enclMethod == null) {
            // Don't check implicit constructors
            return null;
        }

        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();
        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            // Don't type-check arguments of packing calls.
            return p;
        }
        return super.visitMethodInvocation(tree, p);
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        if (TreeUtils.isFieldAccess(node.getVariable())) {
            // Fields can be assigned any value if the receiver is sufficiently unpacked, and cannot be assigned at all
            // otherwise. Nothing to check.
            return null;
        }
        call(() -> super.visitAssignment(node, p), () -> result.illTypedAssignments.add(node));
        return null;
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        call(() -> super.visitVariable(node, p), () -> result.illTypedVars.add(node));

        AnnotatedTypeMirror varType = atypeFactory.getAnnotatedTypeLhs(node);
        ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
        AnnotatedTypeMirror exclType = exclFactory.getAnnotatedTypeLhs(node);

        // Check abstract state for fields and parameters, not for local variables
        if ((methodTree == null || isParam(node)) && !getTypeValidator().dependsOnlyOnAbstractState(varType, exclType, node)) {
            checker.reportError(node, "type.invalid.abstract.state");
        }

        if (enclMethod == null) {
            if (node.getModifiers().getFlags().contains(Modifier.STATIC)) {
                result.addStaticInvariant(
                        getEnclClassName().toString(),
                        new CooperativeVisitor.Invariant(node.getName().toString(), varType));

                if (node.getInitializer() != null) {
                    result.addStaticInitializer(getEnclClassName().toString(), Union.left(node));
                }
            } else {   
            	result.addInstanceInvariant(
            			getEnclClassName().toString(),
            			new CooperativeVisitor.Invariant(node.getName().toString(), varType));

            	if (node.getInitializer() != null) {
                    result.addInstanceInitializer(getEnclClassName().toString(), Union.left(node));
                }
            }
        }

        return null;
    }

    @Override
    public void processClassTree(ClassTree classTree) {
        ClassTree prevEnclClass = enclClass;
        enclClass = classTree;

        super.processClassTree(classTree);

        enclClass = prevEnclClass;
    }

    @Override
    public Void visitMethod(MethodTree node, Void p) {
        MethodTree prevEnclMethod = enclMethod;
        enclMethod = node;

        result.methodOutputTypes.put(node, new AnnotationMirror[node.getParameters().size() + 1]);

        AnnotatedTypeMirror returnType = atypeFactory.getMethodReturnType(node);
        AnnotatedTypeMirror exclReturnType = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class).getMethodReturnType(node);

        if (!(returnType == null || returnType.getKind() == TypeKind.VOID) && !getTypeValidator().dependsOnlyOnAbstractState(returnType, exclReturnType, node)) {
            checker.reportError(node, "return.type.invalid.abstract.state");
        }

        ExecutableElement methodElement = TreeUtils.elementFromDeclaration(node);
        Map<AnnotatedDeclaredType, ExecutableElement> overriddenMethods =
                AnnotatedTypes.overriddenMethods(elements, atypeFactory, methodElement);

        result.overriddenMethods.put(node, overriddenMethods.entrySet().stream().map(e -> Pair.of(
                e.getKey(),
                AnnotatedTypes.asMemberOf(
                        types, atypeFactory, e.getKey(), e.getValue())))
        .collect(Collectors.toList()));

        super.visitMethod(node, p);

        enclMethod = prevEnclMethod;

        return null;
    }

    @Override
    public Void visitBlock(BlockTree node, Void p) {
        boolean prevEnclStaticInitBlock = enclStaticInitBlock;
        boolean prevEnclInstanceInitBlock = enclInstanceInitBlock;

        if (node.isStatic()) {
            enclStaticInitBlock = true;
            result.addStaticInitializer(getEnclClassName().toString(), Union.right(node));
        } else if (enclMethod == null && !enclInstanceInitBlock) {
            enclInstanceInitBlock = true;
            result.addInstanceInitializer(getEnclClassName().toString(), Union.right(node));
        }

        super.visitBlock(node, p);

        enclStaticInitBlock = prevEnclStaticInitBlock;
        enclInstanceInitBlock = prevEnclInstanceInitBlock;

        return null;
    }

    public Name getEnclClassName() {
        return ((JCClassDecl) enclClass).sym.getQualifiedName();
    }

    public Name getEnclMethodNameName() {
        return ((JCMethodDecl) enclMethod).sym.getQualifiedName();
    }

    public LatticeSubchecker getLatticeSubchecker() {
        return (LatticeSubchecker) checker;
    }

    @Override
    public CooperativeChecker getChecker() {
        return (LatticeSubchecker) checker;
    }

    @Override
    public Result getResult() {
        return result;
    }

    @Override
    public CompilationUnitTree getRoot() {
        return root;
    }

    @Override
    public SourcePositions getPositions() {
        return positions;
    }

    protected LatticeTypeValidator getTypeValidator() {
        return (LatticeTypeValidator) typeValidator;
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new LatticeTypeValidator(checker, this, atypeFactory);
    }

    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {
        for (int i = 0; i < requiredArgs.size(); ++i) {
            final int idx = i;
            call(
                    () -> commonAssignmentCheck(
                            requiredArgs.get(idx),
                            passedArgs.get(idx),
                            "argument.type.incompatible", //$NON-NLS-1$
                            paramNames.get(idx).toString(),
                            executableName.toString()),
                    () -> {
                        Tree leaf = getCurrentPath().getLeaf();
                        if (leaf instanceof MethodInvocationTree) {
                            result.addillTypedMethodParam((MethodInvocationTree) getCurrentPath().getLeaf(), idx);
                        } else {
                            result.addillTypedConstructorParam((NewClassTree) getCurrentPath().getLeaf(), idx);
                        }
                    });

            scan(passedArgs.get(i), null);
        }
    }

    @Override
    protected boolean commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        commonAssignmentCheckStartDiagnostic(varType, valueType, valueTree);

        AnnotatedTypeMirror widenedValueType = atypeFactory.getWidenedType(valueType, varType);
        boolean success = atypeFactory.getTypeHierarchy().isSubtype(widenedValueType, varType);

        if (!success && valueTree instanceof LiteralTree) {
            LiteralTree literal = (LiteralTree) valueTree;
            Lattice lattice = getLatticeSubchecker().getTypeFactory().getLattice();
            PropertyAnnotation pa = lattice.getPropertyAnnotation(varType);
            EvaluatedPropertyAnnotation epa = lattice.getEvaluatedPropertyAnnotation(varType);

            if (valueType.getUnderlyingType().toString().equals("java.lang.String") && pa.getAnnotationType().isNonNull()) {
                success = true;
            } else if (epa != null) {
                PropertyAnnotationType pat = epa.getAnnotationType();

                Class<?> literalClass = ClassUtils.literalKindToClass(literal.getKind());
                if (literalClass != null && literalClass.equals(pat.getSubjectType())) {
                    success = epa.checkProperty(literal.getValue());
                } else if (literal.getKind() == Kind.NULL_LITERAL && !pat.getSubjectType().isPrimitive()) {
                    success = epa.checkProperty(null);
                }
            }
        }

        commonAssignmentCheckEndDiagnostic(success, null, varType, valueType, valueTree);

        if (!success) {
            return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
        }

        return success;
    }

    @Override
    protected void checkMethodInvocability(AnnotatedExecutableType method, MethodInvocationTree node) {
        call(
                () -> super.checkMethodInvocability(method, node),
                () -> result.illTypedMethodReceivers.add(node));
    }

    @Override
    protected void checkSuperConstructorCall(MethodInvocationTree superCall) {
        // Nothing to do
    }

    @Override
    protected AnnotationMirror defaultConstructorQualifier(Type classType) {
        return atypeFactory.getTop();
    }

    @Override
    protected void checkImplicitConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);
        if (!qualifierHierarchy.isSubtypeQualifiersOnly(top, constructorAnno) &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isNonNull()) {
            // Report an error instead of a warning.
            checker.reportError(
                    constructorElement, "inconsistent.constructor.type", constructorAnno, top);

            result.illTypedConstructors.add(enclMethod);
        }
    }

    @Override
    protected void checkExplicitConstructorResult(MethodTree tree) {
        AnnotatedExecutableType constructorType = atypeFactory.getAnnotatedType(tree);
        ExecutableElement constructorElement = TreeUtils.elementFromDeclaration(tree);

        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        AnnotationMirror top = atypeFactory.getTop();

        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, top);

        result.methodOutputTypes.get(tree)[0] = constructorAnno;

        if (!qualifierHierarchy.isSubtypeQualifiersOnly(top, constructorAnno) &&
                !atypeFactory.getLattice().getPropertyAnnotation(constructorAnno).getAnnotationType().isNonNull()) {
            // Report an error instead of a warning.
            checker.reportError(
                    constructorElement, "inconsistent.constructor.type", constructorAnno, top);

            result.illTypedConstructors.add(enclMethod);
        }
    }
}
