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
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.*;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeVisitor extends PackingClientVisitor<LatticeAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;
    private final Resolver resolver;
    private final TypeMirror bool;

    private Result result;

    private ClassTree enclClass = null;
    private MethodTree enclMethod = null;
    private boolean enclStaticInitBlock = false;
    private boolean enclInstanceInitBlock = false;

    protected LatticeVisitor(BaseTypeChecker checker, LatticeAnnotatedTypeFactory typeFactory) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
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
        var treeKey = postconditionKey(methodTree, paramIdx);
        var goal = computePostconditionSmt(treeKey, annotation, expression, atypeFactory.getRegularExitStore(methodTree));

        call(
                () -> super.checkPostcondition(methodTree, annotation, expression),
                () -> {
                    if (goal != null) {
                        result.mendingConditions.put(treeKey, goal);
                    }
                    result.addIllTypedMethodOutputParam(methodTree, paramIdx);
                });
    }

    @Override
    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingClientStore<?, ?> exitStore) {
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(TreeUtils.typeOf(param));
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }
        final int paramIdx = TypeUtils.getParameterIndex(methodTree, param);
        var treeKey = postconditionKey(methodTree, paramIdx);
        var annotation = atypeFactory.getAnnotatedTypeLhs(param).getAnnotationInHierarchy(atypeFactory.getTop());
        var goal = computePostconditionSmt(treeKey, annotation, paramExpr, (LatticeStore) exitStore);
        if (!paramsInContract.contains(paramExpr)) {
            result.methodOutputTypes.get(methodTree)[paramIdx] = annotation;
        }
        call(
                () -> super.checkDefaultContract(param, methodTree, exitStore),
                () -> {
                    if (goal != null) {
                        result.mendingConditions.put(treeKey, goal);
                    }
                    result.addIllTypedMethodOutputParam(methodTree, paramIdx);
                });
    }

    private Tree postconditionKey(MethodTree tree, int paramIndex) {
        // postcondition for the receiver: use the method tree as the key (there is no tree for implicit receivers)
        // parameter postcondition: use the variable tree of the parameter
        return paramIndex == 0 ? tree : tree.getParameters().get(paramIndex - 1);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();
        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            // compute smt context for packing calls and put it in result
            // this can later potentially be used to mend uninitialized field errors
            computeSmtContext(atypeFactory.getStoreBefore(tree), tree);
            // Don't type-check arguments of packing calls.
            return p;
        }
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

        // add refinements for all fields in this class and its super classes to the result
        // these are the _declared_ types that may need to be proven later for packing calls.
        addFieldRefinements(classTree);

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
            int paramIndex = i;
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

                if (types.isSameType(valueType.getUnderlyingType(), pat.getSubjectType())) {
                    success = epa.checkProperty(literal.getValue());
                } else if (literal.getKind() == Kind.NULL_LITERAL && !pat.getSubjectType().getKind().isPrimitive()) {
                    success = epa.checkProperty(null);
                }
            }
        }

        commonAssignmentCheckEndDiagnostic(success, null, varType, valueType, valueTree);

        amendSmtResultForValue(varType, valueType, valueTree, success);

        if (!success) {
            return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
        }

        return success;
    }

    @Override
    protected void checkMethodInvocability(AnnotatedExecutableType method, MethodInvocationTree node) {
        if (method.getReceiverType() != null && method.getElement().getKind() != ElementKind.CONSTRUCTOR) {
            AnnotatedTypeMirror methodReceiver = method.getReceiverType().getErased();
            AnnotatedTypeMirror treeReceiver = methodReceiver.shallowCopy(false);
            AnnotatedTypeMirror rcv = this.atypeFactory.getReceiverType(node);
            treeReceiver.addAnnotations(rcv.getEffectiveAnnotations());
            call(() -> {
                this.commonAssignmentCheckStartDiagnostic(methodReceiver, treeReceiver, node);
                boolean success = this.typeHierarchy.isSubtype(treeReceiver, methodReceiver);
                amendSmtResultForReceiver(methodReceiver, rcv, node, success);
                this.commonAssignmentCheckEndDiagnostic(success, null, methodReceiver, treeReceiver, node);
                if (!success) {
                    this.reportMethodInvocabilityError(node, treeReceiver, methodReceiver);
                }
            }, () -> result.illTypedMethodReceivers.add(node));
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

        /* SMT analysis data */

        /**
         * Contains a mapping from "path to ill-typed expression" to
         * "condition that, if proven universally valid, makes the expression well-typed".
         * @see #removeTypeError(TreePath)
         */
        private final Map<Tree, SmtExpression> mendingConditions = new HashMap<>();

        /**
         * Keep track of the refinements of all fields. This can later be used for SMT analysis on packing calls.
         */
        private final Map<VariableElement, SmtExpression> fieldRefinements = new HashMap<>();


        /**
         * Contains a mapping from expression trees to computed contexts.
         * If the expression is well-typed, the context includes the corresponding property refinement.
         */
        private final Map<Tree, Set<SmtExpression>> contexts = new HashMap<>();

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

        private void addContext(Tree tree, SmtExpression formula) {
            CollectionUtils.addToSetMap(contexts, tree, formula);
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

        public Map<Tree, List<VariableElement>> getUninitializedFields() {
            return Collections.unmodifiableMap(uninitializedFields);
        }

        public SmtExpression getFieldRefinement(VariableElement field) {
            return fieldRefinements.get(field);
        }

        public Map<Tree, Set<SmtExpression>> getContexts() {
            return Collections.unmodifiableMap(contexts);
        }

        public Map<Tree, SmtExpression> getMendingConditions() {
            return Collections.unmodifiableMap(mendingConditions);
        }

        public void clear() {
            illTypedAssignments.clear();
            illTypedConstructors.clear();
            illTypedConstructorParams.clear();
            illTypedVars.clear();
            illTypedMethodOutputParams.clear();
            illTypedMethodParams.clear();
            illTypedMethodReceivers.clear();
            illTypedMethodResults.clear();
            overriddenMethods.clear();
            instanceInitializers.clear();
            instanceInvariants.clear();
            staticInitializers.clear();
            staticInvariants.clear();
            methodOutputTypes.clear();
            uninitializedFields.clear();
            mendingConditions.clear();
            contexts.clear();
        }

        public void removeTypeError(TreePath path) {
            Tree tree = path.getLeaf();
            switch (path.getParentPath().getLeaf()) {
                case AssignmentTree a -> illTypedAssignments.remove(a);
                case VariableTree v -> illTypedVars.remove(v);
                case ReturnTree r -> illTypedMethodResults.remove(TreePathUtil.enclosingMethod(path));
                case MethodInvocationTree m -> {
                    // tree is either a parameter or the method select (identifying the receiver)
                    if (tree.equals(m.getMethodSelect())) {
                        illTypedMethodReceivers.remove(m);
                    } else {
                        CollectionUtils.removeFromCollectionMap(illTypedMethodParams, m,
                                TypeUtils.getArgumentIndex(m, tree));
                    }
                }
                case NewClassTree n -> CollectionUtils.removeFromCollectionMap(illTypedConstructorParams, n,
                        TypeUtils.getArgumentIndex(n, tree));
                // postcondition on parameter
                case MethodTree m -> CollectionUtils.removeFromCollectionMap(illTypedMethodOutputParams,
                        m, TypeUtils.getParameterIndex(m, (VariableTree) tree));
                // postcondition on `this`
                case ClassTree c -> CollectionUtils.removeFromCollectionMap(illTypedMethodOutputParams,
                        (MethodTree) tree, 0);
                default -> throw new UnsupportedOperationException("Type error for tree " + tree + " cannot be removed");
            }
        }

        public void removeUninitializedField(Tree packingCall, VariableElement field) {
            CollectionUtils.removeFromCollectionMap(uninitializedFields, packingCall, field);
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

    // parse refinement goal for postcondition, compute and add context to result, return goal (or null)
    @Nullable
    private SmtExpression computePostconditionSmt(
            Tree treeKey, AnnotationMirror annotation,
            JavaExpression subject, LatticeStore exitStore) {


        var property = atypeFactory.getLattice().getPropertyAnnotation(annotation);
        var goal = convertGoal(
                viewpointAdapt(parseOrUnknown(property, getCurrentPath()), List.of(subject)),
                subject.toString()
        );

        if (exitStore != null) {
            computeSmtContext(exitStore, treeKey);
        }

        if (goal != null) {
            return goal.smt();
        }
        return null;
    }

    private void amendSmtResultForReceiver(AnnotatedTypeMirror expectedType, AnnotatedTypeMirror valueType,
                                           MethodInvocationTree invocation, boolean typeCheckSuccess) {
        ExpressionTree receiverTree = TreeUtils.getReceiverTree(invocation);
        JavaExpression subject = receiverTree != null
                ? expressionFromTree(receiverTree)
                : JavaExpression.getImplicitReceiver(TreeUtils.elementFromUse(invocation));
        amendSmtResult(expectedType, valueType, invocation.getMethodSelect(),
                subject, typeCheckSuccess);
    }

    private void amendSmtResultForValue(AnnotatedTypeMirror varType, AnnotatedTypeMirror valueType,
                                        Tree valueTree, boolean typeCheckSuccess) {
        amendSmtResult(varType, valueType, valueTree,
                expressionFromTree((ExpressionTree) valueTree), typeCheckSuccess);
    }

    private void amendSmtResult(
            AnnotatedTypeMirror goalType,
            AnnotatedTypeMirror knownType,
            Tree contextKey,
            JavaExpression subject,
            boolean typeCheckSuccess
    ) {
        var property = atypeFactory.getLattice().getPropertyAnnotation(goalType);

        JavaExpression toProve = viewpointAdapt(
                parseOrUnknown(property, getCurrentPath()),
                List.of(subject)
        );

        JavaToSmtExpression.Result smtGoal = convertGoal(toProve, subject.toString());

        computeSmtContext(atypeFactory.getStoreBefore(contextKey), contextKey);
        var valueProperty = atypeFactory.getLattice().getPropertyAnnotation(knownType);
        var valueRefinement = viewpointAdapt(
                parseOrUnknown(valueProperty, getCurrentPath()),
                List.of(subject)
        );
        tryConvertToSmt(valueRefinement).ifPresent(res -> result.addContext(contextKey, res.smt()));

        if (smtGoal != null) {
            if (typeCheckSuccess) {
                // if we already know that the goal is true (expr is well-typed), we add it to the context
                result.addContext(contextKey, smtGoal.smt());
            } else {
                // if expr is ill-typed, we add the proof goal to the mending conditions
                result.mendingConditions.put(contextKey, smtGoal.smt());
            }
        }
    }

    private JavaExpression expressionFromTree(ExpressionTree tree) {
        // the checker framework expression parser does not support constructor calls yet.
        // but we want to support (pure) constructor calls in property subjects anyway, so we represent them as a
        // special method call. Currently, this only works for top level constructor calls, and not if they're nested
        // in a deeper expression.
        // TODO: allow nested constructor calls as well (need to implement own version of JavaExpression.fromTree for that)
        return tree instanceof NewClassTree nc
                ? JavaExpressionUtil.constructorCall(nc)
                : JavaExpression.fromTree(tree);
    }

    private JavaToSmtExpression.Result convertGoal(JavaExpression goal, String subject) {
        if (goal.containsUnknown()) {
            // checker framework couldn't parse the goal refinement
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses language features not supported by the Checker Framework%n",
                    subject, goal);
            return null;
        }

        // all method calls that appear in the goal must be pure, otherwise we won't do analysis
        var impureScanner = new JavaExpressionScanner<>() {
            boolean found = false;

            @Override
            protected Void visitMethodCall(MethodCall methodCallExpr, Object o) {
                var element = methodCallExpr.getElement();
                if (!atypeFactory.isDeterministic(element) || !atypeFactory.isSideEffectFree(element)) {
                    found = true;
                    return null;
                }
                return super.visitMethodCall(methodCallExpr, o);
            }
        };

        goal.accept(impureScanner, null);

        if (impureScanner.found) {
            System.out.printf("Skipping SMT analysis for expression %s because its refinement %s uses an impure method call%n",
                    subject, goal);
            return null;
        }

        try {
            return JavaToSmtExpression.convert(goal);
        } catch (UnsupportedOperationException e) {
            System.out.printf(
                    "Skipping SMT analysis for expression %s because its refinement %s uses features currently not supported in SMT: %s%n",
                    subject, goal, e.getMessage());
            return null;
        }
    }

    private void computeSmtContext(LatticeStore store, Tree tree) {
        store.allRefinements()
                .flatMap(expr -> tryConvertToSmt(expr).stream())
                .forEach(smtResult -> result.addContext(tree, smtResult.smt()));
    }

    /**
     * Parse the refinement of a PropertyAnnotation to a JavaExpression. If there is a parse error, return Unknown type.
     *
     * @param property PropertyAnnotation
     * @param localVarPath TreePath at which the variables used in the property are available.
     * @return resulting expression, or expression of type Unknown
     */
    private JavaExpression parseOrUnknown(PropertyAnnotation property, TreePath localVarPath) {
        try {
            return property.parseRefinement(localVarPath, checker);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            return new Unknown(bool, property.combinedRefinement("$subject"));
        }
    }

    private JavaExpression parseOrUnknown(PropertyAnnotation property, VariableElement field) {
        try {
            return property.parseRefinement(field, checker);
        } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
            return new Unknown(bool, property.combinedRefinement("$subject"));
        }
    }


    private record MethodCallRefinements(
            JavaExpression returnRefinement,
            JavaExpression receiverRefinement,
            List<JavaExpression> argRefinements
    ) {
    }

    private Optional<JavaToSmtExpression.Result> tryConvertToSmt(JavaExpression expr) {
        try {
            return Optional.of(JavaToSmtExpression.convert(expr));
        } catch (UnsupportedOperationException e) {
            return Optional.empty();
        }
    }

    private void addFieldRefinements(ClassTree classTree) {
        var top = atypeFactory.getTop();
        TypeElement classElement = TreeUtils.elementFromDeclaration(classTree);
        List<VariableElement> fields = ElementUtils.getAllFieldsIn(classElement, elements);
        for (VariableElement field : fields) {
            if (result.fieldRefinements.containsKey(field)) {
                // field refinement in this lattice has already been collected
                continue;
            }
            FieldAccess fieldAccess = new FieldAccess(new ThisReference(field.getEnclosingElement().asType()), field);
            var fieldType = atypeFactory.getAnnotatedType(field);
            if (!qualHierarchy.isSubtypeQualifiersOnly(top, fieldType.getAnnotationInHierarchy(top))) {
                // only include refinement if field type is not a top type
                var property = atypeFactory.getLattice().getPropertyAnnotation(fieldType);
                JavaExpression expr =
                        viewpointAdapt(parseOrUnknown(property, field), List.of(fieldAccess));
                try {
                    result.fieldRefinements.put(field, JavaToSmtExpression.convert(expr).smt());
                } catch (UnsupportedOperationException e) {
                    System.out.printf("Skipping SMT analysis of field %s.%s: %s%n",
                            classElement, field.getSimpleName(), e.getMessage());
                }
            }
        }
    }

}
