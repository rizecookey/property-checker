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
import edu.kit.kastel.property.smt.JavaToSmtExpression;
import edu.kit.kastel.property.smt.SmtExpression;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.util.CollectionUtils;
import org.apache.commons.lang3.function.FailableFunction;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.*;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeVisitor extends PackingClientVisitor<LatticeAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;
    private final Set<VariableTree> localVars;
    private final Resolver resolver;
    private final TypeMirror bool;

    private Result result;

    /**
     * If this is set, we're type checking a method invocation expression, and this object contains the appropriately
     * refinements for the arguments, receiver and return types, viewpoint-adapted to the callsite.
     */
    private MethodCallRefinements invocationContext = null;
    /**
     * When {@link #invocationContext} is not null (i.e. we're checking a method call), paramIndex indicates
     * the index of the parameter whose type we are currently checking against.
     */
    private int paramIndex = -1;
    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;

    protected LatticeVisitor(BaseTypeChecker checker, LatticeAnnotatedTypeFactory typeFactory) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
        localVars = new HashSet<>();
        resolver = new Resolver(checker.getProcessingEnvironment());
        bool = types.getPrimitiveType(TypeKind.BOOLEAN);

        result = new Result(getLatticeSubchecker());
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
            result.methodOutputTypes.get(methodTree)[paramIdx] = atypeFactory.getAnnotatedTypeLhs(param).getAnnotationInHierarchy(atypeFactory.getTop());
        }
        call(
                () -> super.checkDefaultContract(param, methodTree, exitStore),
                () -> result.addIllTypedMethodOutputParam(methodTree, paramIdx));
    }

    @Override
    public Void visitNewClass(NewClassTree tree, Void p) {
        ExecutableElement invokedConstructor = TreeUtils.elementFromUse(tree);
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        // Construct a pseudo method call. We're "pretending" that the constructor is actually a method so that
        // we can reuse the logic for getting the parameter refinements.
        var methodCall = new MethodCall(invokedConstructor.getReturnType(), invokedConstructor, null, arguments);
        // The resulting invocation context doesn't have a return or receiver refinement.
        invocationContext = methodCallRefinements(methodCall);
        return super.visitNewClass(tree, p);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();
        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            // Don't type-check arguments of packing calls.
            return p;
        }
        var receiver = switch (tree.getMethodSelect()) {
            // explicit receiver via member select
            case MemberSelectTree m -> JavaExpression.fromTree(m.getExpression());
            // no explicit receiver
            case IdentifierTree i -> {
                if (ElementUtils.isStatic(invokedMethod)) {
                    // static method => class is the receiver
                    yield new ClassName(invokedMethod.getEnclosingElement().asType());
                } else if (invokedMethod.getReceiverType() != null) {
                    // instance method => this is the receiver
                    yield new ThisReference(invokedMethod.getReceiverType());
                }
                // constructor or initializer without receiver
                yield null;
            }
            default -> null;
        };
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        var methodCall = new MethodCall(invokedMethod.getReturnType(), invokedMethod, receiver, arguments);
        invocationContext = methodCallRefinements(methodCall);
        return super.visitMethodInvocation(tree, p);
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        call(() -> super.visitAssignment(node, p), () -> result.illTypedAssignments.add(node));
        return null;
    }


    @Override
    public Void visitVariable(VariableTree node, Void p) {
        call(() -> super.visitVariable(node, p), () -> result.illTypedVars.add(node));

        localVars.add(node);
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
                        new Invariant(node.getName().toString(), varType));

                if (node.getInitializer() != null) {
                    result.addStaticInitializer(getEnclClassName().toString(), Union.left(node));
                }
            } else {
                result.addInstanceInvariant(
                        getEnclClassName().toString(),
                        new Invariant(node.getName().toString(), varType));

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

        resetLocalVarTracking(node);

        return null;
    }

    private void resetLocalVarTracking(MethodTree tree) {
        localVars.clear();
        localVars.addAll(tree.getParameters());
        if (tree.getReceiverParameter() != null) {
            localVars.add(tree.getReceiverParameter());
        }
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

    protected LatticeTypeValidator getTypeValidator() {
        return (LatticeTypeValidator) typeValidator;
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new LatticeTypeValidator(checker, this, atypeFactory);
    }

    @Override
    protected void checkConstructorInvocation(AnnotatedDeclaredType invocation, AnnotatedExecutableType constructor, NewClassTree newClassTree) {
        super.checkConstructorInvocation(invocation, constructor, newClassTree);
    }

    @Override
    protected void checkArguments(
            List<? extends AnnotatedTypeMirror> requiredArgs,
            List<? extends ExpressionTree> passedArgs,
            CharSequence executableName,
            List<?> paramNames) {
        for (int i = 0; i < requiredArgs.size(); ++i) {
            paramIndex = i;
            call(
                    () -> commonAssignmentCheck(
                            requiredArgs.get(paramIndex),
                            passedArgs.get(paramIndex),
                            "argument.type.incompatible", //$NON-NLS-1$
                            paramNames.get(paramIndex).toString(),
                            executableName.toString()),
                    () -> {
                        Tree leaf = getCurrentPath().getLeaf();
                        if (leaf instanceof MethodInvocationTree) {
                            result.addillTypedMethodParam((MethodInvocationTree) getCurrentPath().getLeaf(), paramIndex);
                        } else {
                            result.addillTypedConstructorParam((NewClassTree) getCurrentPath().getLeaf(), paramIndex);
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
            // compute SMT condition that would remove the type error
            var mendingCondition = computeTypeMendingCondition(varType, valueTree);
            if (mendingCondition != null) {
                // ...and add it to the result
                result.mendingConditions.put(
                        TreePath.getPath(checker.getPathToCompilationUnit(), valueTree),
                        mendingCondition
                );
            }
            return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
        }

        return success;
    }

    @Override
    protected void checkMethodInvocability(AnnotatedExecutableType method, MethodInvocationTree node) {
        AnnotatedDeclaredType expectedType = method.getReceiverType();
        if (expectedType != null && method.getElement().getKind() != ElementKind.CONSTRUCTOR) {
            AnnotatedTypeMirror providedType = atypeFactory.getReceiverType(node);
            // signify that we're checking the receiver type
            paramIndex = -1;
            call(
                    () -> commonAssignmentCheck(
                            expectedType,
                            providedType,
                            node,
                            "method.invocation.invalid",
                            method.getElement(),
                            providedType,
                            expectedType
                    ),
                    () -> result.illTypedMethodReceivers.add(node));
        }
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

    protected void call(Runnable callee, Runnable onError) {
        int startErrorCount = getLatticeSubchecker().getErrorCount();
        callee.run();
        int endErrorCount = getLatticeSubchecker().getErrorCount();
        if (startErrorCount < endErrorCount) {
            onError.run();
        }
        getLatticeSubchecker().setErrorCount(startErrorCount);
    }

    protected String getSourceFileName() {
        return root.getSourceFile().getName();
    }

    protected String getAbsoluteSourceFileName() {
        return Paths.get(root.getSourceFile().getName()).toAbsolutePath().toString();
    }

    protected long getStartLineNumber(Tree tree) {
        return root.getLineMap().getLineNumber(positions.getStartPosition(root, tree));
    }

    protected static boolean isConstructor(MethodTree tree) {
        JCMethodDecl t = (JCMethodDecl) tree;
        return t.name == t.name.table.names.init;
    }

    public void addUninitializedFields(Tree packingStatement, List<VariableElement> uninitFields) {
        result.uninitializedFields.put(packingStatement, uninitFields);
    }

    public static class Result {

        private LatticeSubchecker checker;

        // TODO question: these sets rely on _identity_, i.e. that every tree object is only ever created once for a given position (right?)
        private Set<AssignmentTree> illTypedAssignments = new HashSet<>();
        private Set<VariableTree> illTypedVars = new HashSet<>();
        private Set<MethodTree> illTypedConstructors = new HashSet<>();

        private Set<MethodTree> illTypedMethodResults = new HashSet<>();
        private Map<MethodTree, Set<Integer>> illTypedMethodOutputParams = new HashMap<>();

        private Map<MethodTree, List<Pair<AnnotatedDeclaredType, AnnotatedExecutableType>>> overriddenMethods = new HashMap<>();

        private Map<String, List<Invariant>> instanceInvariants = new HashMap<>();
        private Map<String, List<Invariant>> staticInvariants = new HashMap<>();
        private Map<MethodTree, AnnotationMirror[]> methodOutputTypes = new HashMap<>();

        private Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> instanceInitializers = new HashMap<>();
        private Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> staticInitializers = new HashMap<>();
        private Map<MethodInvocationTree, Set<Integer>> illTypedMethodParams = new HashMap<>();
        private Set<MethodInvocationTree> illTypedMethodReceivers = new HashSet<>();
        private Map<NewClassTree, Set<Integer>> illTypedConstructorParams = new HashMap<>();

        private Map<Tree, List<VariableElement>> uninitializedFields = new HashMap<>();

        /**
         * Contains a mapping from "path to ill-typed expression" to
         * "condition that, if proven universally valid, makes the expression well-typed".
         * @see #removeTypeError(TreePath)
         */
        private final Map<TreePath, SmtTypeMendingCondition> mendingConditions = new HashMap<>();

        private Result(LatticeSubchecker checker) {
            this.checker = checker;
        }

        public LatticeSubchecker getChecker() {
            return checker;
        }

        public LatticeAnnotatedTypeFactory getTypeFactory() {
            return checker.getTypeFactory();
        }

        public Lattice getLattice() {
            return getTypeFactory().getLattice();
        }

        public boolean isWellTyped(AssignmentTree tree) {
            return !illTypedAssignments.contains(tree);
        }

        public boolean isWellTyped(VariableTree tree) {
            return !illTypedVars.contains(tree);
        }

        public boolean isWellTypedConstructor(MethodTree tree) {
            if (!isConstructor(tree)) {
                throw new IllegalArgumentException();
            }

            return !illTypedConstructors.contains(tree);
        }

        public boolean isWellTypedMethodResult(MethodTree tree) {
            return !illTypedMethodResults.contains(tree);
        }

        private void addInstanceInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(instanceInvariants, className, invariant);
        }

        private void addStaticInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(staticInvariants, className, invariant);
        }

        private void addInstanceInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(instanceInitializers, className, init);
        }

        private void addStaticInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(staticInitializers, className, init);
        }

        private void addillTypedMethodParam(MethodInvocationTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedMethodParams, tree, param);
        }

        private void addillTypedConstructorParam(NewClassTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedConstructorParams, tree, param);
        }

        private void addIllTypedMethodOutputParam(MethodTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedMethodOutputParams, tree, param);
        }

        public List<Pair<AnnotatedDeclaredType, AnnotatedExecutableType>> getOverriddenMethods(MethodTree tree) {
            return CollectionUtils.getUnmodifiableList(overriddenMethods, tree);
        }

        public List<Invariant> getInstanceInvariants(String className) {
            return CollectionUtils.getUnmodifiableList(instanceInvariants, className);
        }

        public List<Invariant> getStaticInvariants(String className) {
            return CollectionUtils.getUnmodifiableList(staticInvariants, className);
        }

        public List<Union<StatementTree, VariableTree, BlockTree>> getInstanceInitializers(String className) {
            return CollectionUtils.getUnmodifiableList(instanceInitializers, className);
        }

        public List<Union<StatementTree, VariableTree, BlockTree>> getStaticInitializers(String className) {
            return CollectionUtils.getUnmodifiableList(staticInitializers, className);
        }

        public List<AnnotationMirror> getMethodOutputTypes(MethodTree tree) {
            return methodOutputTypes.containsKey(tree)
                    ? Collections.unmodifiableList(Arrays.asList(methodOutputTypes.get(tree)))
                    : List.of();
        }

        public Set<Integer> getIllTypedMethodParams(MethodInvocationTree tree) {
            return CollectionUtils.getUnmodifiableSet(illTypedMethodParams, tree);
        }

        public Set<MethodInvocationTree> getIllTypedMethodReceivers() {
            return Collections.unmodifiableSet(illTypedMethodReceivers);
        }

        public Set<Integer> getIllTypedConstructorParams(NewClassTree tree) {
            return CollectionUtils.getUnmodifiableSet(illTypedConstructorParams, tree);
        }

        public Set<Integer> getIllTypedMethodOutputParams(MethodTree tree) {
            return CollectionUtils.getUnmodifiableSet(illTypedMethodOutputParams, tree);
        }

        public List<VariableElement> getUninitializedFields(Tree tree) {
            return CollectionUtils.getUnmodifiableList(uninitializedFields, tree);
        }

        public void removeTypeError(TreePath path) {
            Tree tree = path.getLeaf();
            switch (path.getParentPath().getLeaf()) {
                case AssignmentTree a -> illTypedAssignments.remove(a);
                case VariableTree v -> illTypedVars.remove(v);
                case ReturnTree r -> illTypedMethodResults.remove(TreePathUtil.enclosingMethod(path));
                case MethodInvocationTree m -> {
                    // tree is either a parameter or a receiver
                    if (tree.equals(m.getMethodSelect())) {
                        illTypedMethodReceivers.remove(m);
                    } else {
                        // TODO verify that only one argument can match tree
                        for (int i = 0; i < m.getArguments().size(); i++) {
                            if (m.getArguments().get(i).equals(tree)) {
                                CollectionUtils.removeFromCollectionMap(illTypedMethodParams, m, i);
                            }
                        }
                    }
                }
                case NewClassTree n -> {
                    for (int i = 0; i < n.getArguments().size(); i++) {
                        if (n.getArguments().get(i).equals(tree)) {
                            CollectionUtils.removeFromCollectionMap(illTypedConstructorParams, n, i);
                        }
                    }
                }
                default -> throw new UnsupportedOperationException("Type error for path " + path + " cannot be removed");
            }
        }

        // TODO: when is this actually called? only when merging results from two checkers of the same kind? shouldn't they produce equal results?
        public void addAll(Result result) {
            illTypedAssignments.addAll(result.illTypedAssignments);
            illTypedVars.addAll(result.illTypedVars);
            illTypedConstructors.addAll(result.illTypedConstructors);

            illTypedMethodResults.addAll(result.illTypedMethodResults);
            illTypedMethodOutputParams.putAll(result.illTypedMethodOutputParams);

            overriddenMethods.putAll(result.overriddenMethods);
            instanceInvariants.putAll(result.instanceInvariants);
            staticInvariants.putAll(result.staticInvariants);
            instanceInitializers.putAll(result.instanceInitializers);
            staticInitializers.putAll(result.staticInitializers);

            illTypedMethodParams.putAll(result.illTypedMethodParams);
            illTypedMethodReceivers.addAll(result.illTypedMethodReceivers);
            illTypedConstructorParams.putAll(result.illTypedConstructorParams);

            uninitializedFields.putAll(result.uninitializedFields);
        }
    }

    /**
     * Represents an implication that, if proven universally valid in SMT, shows that an expression is well-typed.
     * The implication is the conjunction of the context => goal.
     *
     * @param context Formulae providing constraints for the goal.
     * @param goal    Formula that must be proven universally valid in the given context
     */
    public record SmtTypeMendingCondition(Set<SmtExpression> context, SmtExpression goal) {

    }

    public static class Invariant {

        private String fieldName;
        private AnnotatedTypeMirror type;

        private Invariant(String fieldName, AnnotatedTypeMirror type) {
            this.fieldName = fieldName;
            this.type = type;
        }

        public String getFieldName() {
            return fieldName;
        }

        public AnnotatedTypeMirror getType() {
            return type;
        }
    }

    /* ==== SMT SOLVING CODE ==== */

    private SmtTypeMendingCondition computeTypeMendingCondition(AnnotatedTypeMirror varType, Tree valueExpTree) {
        // TODO: verify that all context formulae are actually boolean (is this already done elsewhere?)

        JavaExpression toProve;
        if (getCurrentPath().getParentPath() instanceof MethodInvocationTree) {
            if (invocationContext == null) {
                // no invocation context means no refinements are available for this argument
                return null;
            }
            toProve = paramIndex == -1
                    ? invocationContext.receiverRefinement
                    : invocationContext.argRefinements.get(paramIndex);
        } else {
            String refinement = getRefinement(varType, valueExpTree);
            toProve = parseOrUnknown(refinement, ref -> StringToJavaExpression.atPath(ref, getCurrentPath(), checker));
        }

        if (toProve instanceof Unknown) {
            // checker framework couldn't parse the goal refinement
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses language features not supported by the Checker Framework%n",
                    valueExpTree, toProve);
            return null;
        }

        JavaToSmtExpression.Result goal;
        try {
            goal = JavaToSmtExpression.convert(toProve);
        } catch (UnsupportedOperationException e) {
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses features currently not supported in SMT: %s%n",
                    valueExpTree, toProve, e.getMessage());
            return null;
        }

        return new SmtTypeMendingCondition(context(goal.references()), goal.smt());
    }


    private Set<SmtExpression> context(Collection<JavaExpression> initialRefs) {
        Set<JavaExpression> visited = new HashSet<>();
        Queue<JavaExpression> refs = new ArrayDeque<>(initialRefs);
        Set<SmtExpression> context = new HashSet<>();

        // collect all locally available refinements (params + vars)
        List<JavaExpression> localRefinements = new ArrayList<>();
        for (VariableTree local : localVars) {
            if (local != methodTree.getReceiverParameter()
                    && resolver.findLocalVariableOrParameter(local.getName().toString(), getCurrentPath()) == null) {
                continue;
            }
            AnnotatedTypeMirror type = atypeFactory.getAnnotatedType(local);
            String refinement = getRefinement(type, local.getName());
            JavaExpression expr = parseOrUnknown(refinement, ref -> StringToJavaExpression.atPath(ref, getCurrentPath(), checker));
            if (!(expr instanceof Unknown)) {
                localRefinements.add(expr);
            }

        }

        while (!refs.isEmpty()) {
            // reference is always viewpoint-adapted from original context
            JavaExpression ref = refs.remove();
            if (visited.contains(ref) || hasCycle(ref)) {
                continue;
            }

            System.out.println("Finding constraints for: " + ref);

            // search in local refinements for mentions of the reference
            Stream<JavaExpression> relevantLocalRefinements =
                    localRefinements.stream().filter(expr -> expr.containsSyntacticEqualJavaExpression(ref));

            // find constraints for reference/expression
            Collection<JavaExpression> refinements = switch (ref) {
                case FieldAccess f -> constraintsForField(visited, f);
                case MethodCall m -> List.of(methodCallClause(m));
                // constraints for local vars and params have already been added in local refinement search
                default -> Collections.emptyList();
            };

            Stream.concat(relevantLocalRefinements, refinements.stream())
                    .map(expr -> {
                        System.out.print(expr);
                        try {
                            var smt = JavaToSmtExpression.convert(expr);
                            System.out.println();
                            return smt;
                        } catch (UnsupportedOperationException e) {
                            System.out.printf(" (skipped because: %s)%n", e.getMessage());
                            return null;
                        }
                    })
                    .filter(Objects::nonNull)
                    .forEach(result -> {
                        context.add(result.smt());
                        refs.addAll(result.references());
                    });
            visited.add(ref);
        }
        return context;
    }

    // this is basically a shortcut for "refinement + external references"
    private Collection<JavaExpression> constraintsForField(Set<JavaExpression> visited, FieldAccess fieldAccess) {
        List<JavaExpression> results = new ArrayList<>();

        // go through all parent receivers of field access to find references
        // field could be further constrained by other local refinements, but these aren't handled here
        for (JavaExpression e = fieldAccess; e instanceof FieldAccess fa; e = fa.getReceiver()) {
            TypeMirror receiverType = fa.getReceiver().getType();

            for (VariableElement field : ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(receiverType), elements)) {
                JavaExpression localFieldRef = new FieldAccess(new ThisReference(receiverType), field);

                if (visited.contains(viewpointAdapt(localFieldRef, fa.getReceiver()))) {
                    // we have already handled this field and all its dependencies
                    continue;
                }

                AnnotatedTypeMirror type = atypeFactory.getAnnotatedType(field);
                String refinement = getRefinement(type, localFieldRef);
                JavaExpression expr = viewpointAdapt(
                        parseOrUnknown(refinement,
                                r -> StringToJavaExpression.atFieldDecl(refinement, field, checker)),
                        fa.getReceiver()
                );

                // if refinement references the original field we're interested in, add it to the result
                if (expr.containsSyntacticEqualJavaExpression(fieldAccess)) {
                    results.add(expr);
                }
            }
        }

        return results;
    }

    /**
     * Parse a refinement string to a JavaExpression. If there is a parse error, return Unknown type.
     *
     * @param refinement boolean expression as a string
     * @param parser     Function that parses the refinement string
     * @return resulting expression, or expression of type Unknown
     */
    private JavaExpression parseOrUnknown(
            String refinement,
            FailableFunction<String, ? extends JavaExpression, JavaExpressionParseUtil.JavaExpressionParseException> parser) {
        try {
            return parser.apply(refinement);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            return new Unknown(bool, refinement);
        }
    }

    // TODO: check if method can actually be used (purity)
    private JavaExpression methodCallClause(MethodCall method) {
        var refinements = methodCallRefinements(method);
        if (refinements == null || refinements.returnRefinement() instanceof Unknown) {
            // either method source code is not available or the refinement for the return value could not be parsed
            // => no dependent type analysis possible
            return new ValueLiteral(bool, true);
        }

        // construct the formula arg (including receiver) refinements => return refinement
        JavaExpression argumentConjunction = Stream.concat(
                        Stream.of(refinements.receiverRefinement()),
                        refinements.argRefinements().stream()
                ).filter(expr -> !(expr instanceof Unknown))
                .reduce(new ValueLiteral(bool, true), (l, r) -> new BinaryOperation(bool, Tree.Kind.AND, l, r));
        return new BinaryOperation(
                bool, Tree.Kind.OR,
                new UnaryOperation(bool, Tree.Kind.LOGICAL_COMPLEMENT, argumentConjunction), refinements.returnRefinement()
        );
    }

    private record MethodCallRefinements(
            JavaExpression returnRefinement,
            JavaExpression receiverRefinement,
            List<JavaExpression> argRefinements
    ) {
    }

    // Given a method call expression, returns the callsite-adapted refinements for the return and argument values as JavaExpressions.
    private MethodCallRefinements methodCallRefinements(MethodCall method) {
        AnnotatedTypeMirror.AnnotatedExecutableType type = atypeFactory.getAnnotatedType(method.getElement());
        TreePath methodPath = trees.getPath(method.getElement());

        if (methodPath == null) {
            // method source is not available; no context available
            return null;
        }

        boolean constructorCall = method.getElement().getKind() != ElementKind.CONSTRUCTOR;

        // parameter elements -> checker framework representation
        Map<VariableElement, FormalParameter> params = JavaExpression.getFormalParameters(method.getElement()).stream()
                .collect(Collectors.toMap(FormalParameter::getElement, Function.identity()));

        JavaExpression receiver = method.getReceiver();

        // Function that parses a declaration-level expression, where parameters are referenced by name
        Function<String, JavaExpression> parser = refinement -> {
            // 1. parse refinement in method body scope
            JavaExpression expression;
            try {
                expression = StringToJavaExpression.atPath(refinement, methodPath, checker);
            } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                expression = new Unknown(bool, refinement);
            }

            // 2. convert nominal parameter references to FormalParameters
            expression = expression.accept(new JavaExpressionConverter() {
                @Override
                protected JavaExpression visitLocalVariable(LocalVariable localVarExpr, Void unused) {
                    return params.get(localVarExpr.getElement());
                }
            }, null);
            // 3. viewpoint adapt to call site
            return viewpointAdapt(expression, receiver, method.getArguments());
        };

        List<JavaExpression> argRefinements = new ArrayList<>();
        for (VariableElement parameter : method.getElement().getParameters()) {
            String refinement = getRefinement(atypeFactory.getAnnotatedType(parameter), parameter.getSimpleName());
            argRefinements.add(parser.apply(refinement));
        }

        // Receiver parameter `this` may have refinements too
        // If there is no receiver or it's a constructor, it's just "true" (method can always be called)
        JavaExpression receiverRefinement =
                type.getReceiverType() == null || constructorCall
                        ? new ValueLiteral(bool, true)
                        : parser.apply(getRefinement(type.getReceiverType(), method.getReceiver()));

        // return value refinement, unless the method returns void (equivalent to top type)
        // or it's a constructor (expression syntax doesn't support constructor calls)
        JavaExpression returnRefinement = type.getReturnType().getKind() == TypeKind.VOID || constructorCall
                ? new ValueLiteral(bool, true)
                : parser.apply(getRefinement(type.getReturnType(),
                // the input method call with parameters and receiver simplified
                new MethodCall(
                        method.getType(),
                        method.getElement(),
                        receiver instanceof ClassName ? receiver : new ThisReference(receiver.getType()),
                        List.copyOf(JavaExpression.getFormalParameters(method.getElement()))
                )));
        return new MethodCallRefinements(returnRefinement, receiverRefinement, argRefinements);
    }

    private String getRefinement(AnnotatedTypeMirror type, Object subject) {
        PropertyAnnotation anno = atypeFactory.getLattice().getPropertyAnnotation(type);
        String property = anno.getAnnotationType().getProperty()
                .replace("§subject§", "(" + subject + ")");
        String wfCondition = anno.getAnnotationType().getWFCondition()
                .replace("§subject§", "(" + subject + ")");
        var actualParams = anno.getActualParameters().iterator();
        for (PropertyAnnotationType.Parameter param : anno.getAnnotationType().getParameters()) {
            String actual = "(" + actualParams.next() + ")";
            String placeholder = "§" + param.getName() + "§";
            wfCondition = wfCondition.replace(placeholder, actual);
            property = property.replace(placeholder, actual);
        }
        return String.format("(%s) && (%s)", wfCondition, property);
    }

    private boolean hasCycle(JavaExpression expr) {
        Set<Element> visited = new HashSet<>();
        Element element;
        // detect when an element reappears in a chain of method calls/fields
        do {
            switch (expr) {
                case MethodCall m -> {
                    expr = m.getReceiver();
                    element = m.getElement();
                }
                case FieldAccess f -> {
                    expr = f.getReceiver();
                    element = f.getField();
                }
                default -> {
                    return false;
                }
            }
        } while (visited.add(element));
        return true;
    }

}
