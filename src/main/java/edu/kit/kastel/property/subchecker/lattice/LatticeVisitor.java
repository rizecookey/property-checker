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
import edu.kit.kastel.property.smt.SmtCompiler;
import edu.kit.kastel.property.smt.SmtExpression;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.util.CollectionUtils;
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
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.SolverException;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.nio.file.Paths;
import java.util.*;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.stream.Collectors;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public final class LatticeVisitor extends PackingClientVisitor<LatticeAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;
    private final Set<VariableTree> localVars;
    private final Resolver resolver;

    private Result result;

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
    public Void visitMethodInvocation(MethodInvocationTree tree, Void p) {
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
            // TODO: does getParameters() contain receiver parameter already?
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

    // TODO: can we have multiple commonAssignmentCheck overloads next to each other?
    @Override
    protected boolean commonAssignmentCheck(AnnotatedTypeMirror varType, ExpressionTree valueExpTree, @CompilerMessageKey String errorKey, Object... extraArgs) {
        return smtBasedAssignmentCheck(varType, valueExpTree);
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

    // TODO: refactor to include, for each type error, the smt context and goal to discharge it
    // we need to able to combine the contexts from all sub checkers for a given tree later
    // (find a suitable data structure for this - map could work)
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

    private boolean smtBasedAssignmentCheck(AnnotatedTypeMirror varType, ExpressionTree valueExpTree) {
        System.out.printf("assignment check: expr %s to type %s%n", valueExpTree, varType);

        // TODO: verify that all context formulae are actually boolean

        try (var solverContext = SolverContextFactory.createSolverContext(SolverContextFactory.Solvers.SMTINTERPOL);
             var proverEnv = solverContext.newProverEnvironment()) {
            SmtCompiler compiler = new SmtCompiler(solverContext);
            JavaExpression toProve = StringToJavaExpression.atPath(getRefinement(varType, valueExpTree), getCurrentPath(), checker);
            JavaToSmtExpression.Result goal = JavaToSmtExpression.convert(toProve);
            var bmgr = solverContext.getFormulaManager().getBooleanFormulaManager();
            List<BooleanFormula> conjunction = new ArrayList<>();

            // add goal
            try {
                conjunction.add(bmgr.not((BooleanFormula) compiler.compile(goal.smt())));
            } catch (UnsupportedOperationException e) {
                System.out.printf("Skipping proof goal %s due to use of unsupported feature: %s%n",
                        goal.smt(), e.getMessage());
                return false;
            }

            Set<SmtExpression> context = context(goal.references());
            System.out.println("Context: " + context);
            System.out.println("Goal to prove: " + goal.smt());

            // add context formulae
            for (SmtExpression expr : context) {
                try {
                    conjunction.add((BooleanFormula) compiler.compile(expr));
                } catch (UnsupportedOperationException e) {
                    // drop context constraints that aren't representable
                    System.out.printf("Ignoring context formula %s due to use of unsupported feature: %s%n",
                            expr, e.getMessage());
                }
            }

            // conjunction of context and complement of goal
            // == (context =/> goal)
            // if this is unsatisfiable, context => goal is universally valid
            proverEnv.addConstraint(bmgr.and(conjunction));
            var assignmentValid = proverEnv.isUnsat();
            System.out.println("Could be proven? " + assignmentValid);
            if (assignmentValid) {
                return true;
            }
        } catch (InvalidConfigurationException | InterruptedException | SolverException |
                 JavaExpressionParseUtil.JavaExpressionParseException e) {
            throw new RuntimeException(e);
        }

        return false;
    }


    private Set<SmtExpression> context(Collection<JavaExpression> initialRefs) throws JavaExpressionParseUtil.JavaExpressionParseException {
        Set<JavaExpression> visited = new HashSet<>();
        Queue<JavaExpression> refs = new ArrayDeque<>(initialRefs);
        Set<SmtExpression> context = new HashSet<>();

        Consumer<JavaToSmtExpression.Result> addToContext = result -> {
            context.add(result.smt());
            refs.addAll(result.references());
        };

        // collect all locally available refinements (params + vars)
        List<JavaExpression> localRefinements = new ArrayList<>();
        for (VariableTree local : localVars) {
            if (local != methodTree.getReceiverParameter()
                    && resolver.findLocalVariableOrParameter(local.getName().toString(), getCurrentPath()) == null) {
                continue;
            }
            AnnotatedTypeMirror type = atypeFactory.getAnnotatedType(local);
            String refinement = getRefinement(type, local.getName());
            localRefinements.add(StringToJavaExpression.atPath(refinement, getCurrentPath(), checker));
        }

        while (!refs.isEmpty()) {
            // reference is always viewpoint-adapted from original context
            JavaExpression ref = refs.remove();
            if (visited.contains(ref) || hasCycle(ref)) {
                continue;
            }

            System.out.println("Finding constraints for: " + ref);

            // search in local refinements for mentions of the reference
            localRefinements.stream()
                    .filter(expr -> expr.containsSyntacticEqualJavaExpression(ref))
                    .peek(System.out::println)
                    .map(JavaToSmtExpression::convert)
                    .forEach(addToContext);

            // find constraints for reference/expression
            Collection<JavaExpression> refinements = switch (ref) {
                case FieldAccess f -> constraintsForField(visited, f);
                case MethodCall m -> List.of(methodCallClause(m));
                // constraints for local vars and params have already been added in local refinement search
                default -> Collections.emptyList();
            };

            refinements.stream().peek(System.out::println).map(JavaToSmtExpression::convert).forEach(addToContext);
            visited.add(ref);
        }
        return context;
    }

    // TODO expand all class names to be fully qualified so they work everywhere (and receiver is normalised)

    // this is basically a shortcut for "refinement + external references"
    private Collection<JavaExpression> constraintsForField(Set<JavaExpression> visited, FieldAccess fieldAccess) throws JavaExpressionParseUtil.JavaExpressionParseException {
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
                        StringToJavaExpression.atFieldDecl(refinement, field, checker),
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

    // TODO: check if method can actually be used
    private JavaExpression methodCallClause(MethodCall method) throws JavaExpressionParseUtil.JavaExpressionParseException {
        AnnotatedTypeMirror.AnnotatedExecutableType type = atypeFactory.getAnnotatedType(method.getElement());
        TreePath methodPath = trees.getPath(method.getElement());

        // parameter elements -> checker framework representation
        Map<VariableElement, FormalParameter> params = JavaExpression.getFormalParameters(method.getElement()).stream()
                .collect(Collectors.toMap(FormalParameter::getElement, Function.identity()));

        interface ParsingFunction {
            JavaExpression parse(String expr) throws JavaExpressionParseUtil.JavaExpressionParseException;
        }

        JavaExpression receiver = method.getReceiver();

        // Function that parses a declaration-level expression, where parameters are referenced by name
        ParsingFunction function = refinement -> {
            // 1. parse refinement in method body scope
            JavaExpression expression = StringToJavaExpression.atPath(refinement, methodPath, checker);
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
            argRefinements.add(function.parse(refinement));
        }

        // the input method call with parameters and receiver simplified
        MethodCall unadaptedReturn = new MethodCall(
                method.getType(),
                method.getElement(),
                receiver instanceof ClassName ? receiver : new ThisReference(receiver.getType()),
                List.copyOf(JavaExpression.getFormalParameters(method.getElement()))
        );

        // construct the formula arg refinements => return refinement
        JavaExpression returnRefinement = function.parse(getRefinement(type.getReturnType(), unadaptedReturn));
        TypeMirror bool = types.getPrimitiveType(TypeKind.BOOLEAN);
        JavaExpression argumentConjunction = argRefinements.stream().reduce(new ValueLiteral(bool, true),
                (l, r) -> new BinaryOperation(bool, Tree.Kind.AND, l, r));
        return new BinaryOperation(
                bool, Tree.Kind.OR,
                new UnaryOperation(bool, Tree.Kind.LOGICAL_COMPLEMENT, argumentConjunction),
                returnRefinement
        );
    }

    private String getRefinement(AnnotatedTypeMirror type, Object subject) {
        PropertyAnnotation anno = atypeFactory.getLattice().getPropertyAnnotation(type);
        String refinement = anno.getAnnotationType().getProperty();
        var actualParams = anno.getActualParameters().iterator();
        for (PropertyAnnotationType.Parameter param : anno.getAnnotationType().getParameters()) {
            refinement = refinement.replace("§" + param.getName() + "§", "(" + actualParams.next() + ")");
        }
        return refinement.replace("§subject§", "(" + subject + ")");
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
