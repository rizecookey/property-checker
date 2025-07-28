package edu.kit.kastel.property.subchecker.lattice;

import com.sun.source.tree.*;
import com.sun.source.util.SourcePositions;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.util.CollectionUtils;
import edu.kit.kastel.property.util.Union;
import org.apache.commons.lang3.tuple.Triple;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.Pair;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import java.nio.file.Paths;
import java.util.*;

public interface CooperativeVisitor {

    static boolean isConstructor(MethodTree tree) {
        JCTree.JCMethodDecl t = (JCTree.JCMethodDecl) tree;
        return t.name == t.name.table.names.init;
    }

    CooperativeChecker getChecker();
    GenericAnnotatedTypeFactory<?,?,?,?> getTypeFactory();
    Result getResult();
    CompilationUnitTree getRoot();
    SourcePositions getPositions();

    default Lattice getLattice() {
        return getChecker().getLattice();
    }

    default void call(Runnable callee, Runnable onError) {
        int startErrorCount = getChecker().getErrorCount();
        callee.run();
        int endErrorCount = getChecker().getErrorCount();
        if (startErrorCount < endErrorCount) {
            onError.run();
        }
        getChecker().setErrorCount(startErrorCount);
    }

    default String getSourceFileName() {
        return getRoot().getSourceFile().getName();
    }

    default String getAbsoluteSourceFileName() {
        return Paths.get(getRoot().getSourceFile().getName()).toAbsolutePath().toString();
    }

    default long getStartLineNumber(Tree tree) {
        return getRoot().getLineMap().getLineNumber(getPositions().getStartPosition(getRoot(), tree));
    }

    default void addUninitializedFields(Tree packingStatement, List<VariableElement> uninitFields) {
        getResult().uninitializedFields.put(packingStatement, uninitFields);
    }

    class Result {

        private CooperativeChecker checker;

        public Set<AssignmentTree> illTypedAssignments = new HashSet<>();
        public Set<VariableTree> illTypedVars = new HashSet<>();
        public Set<MethodTree> illTypedConstructors = new HashSet<>();

        public Set<MethodTree> illTypedMethodResults = new HashSet<>();
        public Map<MethodTree, Set<Integer>> illTypedMethodOutputParams = new HashMap<>();

        public Map<MethodTree, List<Pair<AnnotatedTypeMirror.AnnotatedDeclaredType, AnnotatedTypeMirror.AnnotatedExecutableType>>> overriddenMethods = new HashMap<>();

        public Map<String, List<Invariant>> instanceInvariants = new HashMap<>();
        public Map<String, List<Invariant>> staticInvariants = new HashMap<>();
        public Map<MethodTree, AnnotationMirror[]> methodOutputTypes = new HashMap<>();

        public Map<MethodTree, List<Pair<AnnotationMirror, JavaExpression>>> nullnessPostconditions = new HashMap<>();
        public Map<MethodTree, List<Triple<AnnotationMirror, JavaExpression, Boolean>>> nullnessCondPostconditions = new HashMap<>();

        public Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> instanceInitializers = new HashMap<>();
        public Map<String, List<Union<StatementTree, VariableTree, BlockTree>>> staticInitializers = new HashMap<>();
        public Map<MethodInvocationTree, Set<Integer>> illTypedMethodParams = new HashMap<>();
        public Set<MethodInvocationTree> illTypedMethodReceivers = new HashSet<>();
        public Map<NewClassTree, Set<Integer>> illTypedConstructorParams = new HashMap<>();

        public Map<Tree, List<VariableElement>> uninitializedFields = new HashMap<>();

        public Result(CooperativeChecker checker) {
            this.checker = checker;
        }

        public CooperativeChecker getChecker() {
            return checker;
        }

        public GenericAnnotatedTypeFactory<?,?,?,?> getTypeFactory() {
            return (GenericAnnotatedTypeFactory<?, ?, ?, ?>) checker.getTypeFactory();
        }

        public Lattice getLattice() {
            return getChecker().getLattice();
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

        public void addInstanceInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(instanceInvariants, className, invariant);
        }

        public void addStaticInvariant(String className, Invariant invariant) {
            CollectionUtils.addToListMap(staticInvariants, className, invariant);
        }

        public void addInstanceInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(instanceInitializers, className, init);
        }

        public void addStaticInitializer(String className, Union<StatementTree, VariableTree, BlockTree> init) {
            CollectionUtils.addToListMap(staticInitializers, className, init);
        }

        public void addillTypedMethodParam(MethodInvocationTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedMethodParams, tree, param);
        }

        public void addillTypedConstructorParam(NewClassTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedConstructorParams, tree, param);
        }

        public void addIllTypedMethodOutputParam(MethodTree tree, int param) {
            CollectionUtils.addToSetMap(illTypedMethodOutputParams, tree, param);
        }

        public List<Pair<AnnotatedTypeMirror.AnnotatedDeclaredType, AnnotatedTypeMirror.AnnotatedExecutableType>> getOverriddenMethods(MethodTree tree) {
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

        public Map<MethodTree, List<Pair<AnnotationMirror, JavaExpression>>> getNullnessPostconditions() {
            return nullnessPostconditions;
        }

        public Map<MethodTree, List<Triple<AnnotationMirror, JavaExpression, Boolean>>> getNullnessCondPostconditions() {
            return nullnessCondPostconditions;
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

        public Invariant(String fieldName, AnnotatedTypeMirror type) {
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
}
