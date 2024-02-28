package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.TargetType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.Element;
import javax.lang.model.element.ExecutableElement;
import java.util.HashSet;
import java.util.Set;
import java.util.stream.Collectors;

public abstract class PackingClientVisitor<
        Factory extends PackingClientAnnotatedTypeFactory<
                ? extends PackingClientValue<?>,
                ? extends PackingClientStore<?, ?>,
                ? extends PackingClientTransfer<?, ?, ?>,
                ? extends PackingClientAnalysis<?, ?, ?>>>
        extends BaseTypeVisitor<Factory> {

    protected Set<JavaExpression> paramsInContract = new HashSet<>();

    public PackingClientVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    protected PackingClientVisitor(BaseTypeChecker checker, @Nullable Factory typeFactory) {
        super(checker, typeFactory);
    }

    @Override
    protected void checkPostcondition(MethodTree methodTree, AnnotationMirror annotation, JavaExpression expression) {
        paramsInContract.add(expression);
        CFAbstractStore<?, ?> exitStore = atypeFactory.getRegularExitStore(methodTree);
        if (exitStore == null) {
            // If there is no regular exitStore, then the method cannot reach the regular exit and
            // there is no need to check anything.
        } else {
            CFAbstractValue<?> value = exitStore.getValue(expression);
            AnnotationMirror inferredAnno = null;
            if (value != null) {
                AnnotationMirrorSet annos = value.getAnnotations();
                inferredAnno = qualHierarchy.findAnnotationInSameHierarchy(annos, annotation);
            }
            if (!checkContract(expression, annotation, inferredAnno, exitStore)) {
                checker.reportError(
                        methodTree,
                        getContractPostconditionNotSatisfiedMessage(),
                        methodTree.getName(),
                        contractExpressionAndType(expression.toString(), inferredAnno),
                        contractExpressionAndType(expression.toString(), annotation));
            }
        }
    }

    protected abstract AnnotationMirror defaultConstructorQualifier(Type classType);

    @Override
    public Void visitMethod(MethodTree tree, Void p) {
        super.visitMethod(tree, p);

        // check that params not covered by explicit contract fulfill their input type
        VariableTree receiver = tree.getReceiverParameter();
        if (receiver != null) {
            checkDefaultContract(receiver, tree, atypeFactory.getRegularExitStore(tree));
        }
        for (VariableTree param : tree.getParameters()) {
            checkDefaultContract(param, tree, atypeFactory.getRegularExitStore(tree));
        }


        if (TreeUtils.isConstructor(tree) && ! TreeUtils.isSynthetic(tree)) {
            checkExplicitConstructorResult(tree);
        }

        return p;
    }

    @Override
    protected final void checkConstructorResult(AnnotatedTypeMirror.AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // Explicit constructurs are treated by ::checkExplicitConstructorResult, which is called directly by visitMethod.
        checkImplicitConstructorResult(constructorType, constructorElement);
    }

    protected void checkImplicitConstructorResult(AnnotatedTypeMirror.AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        super.checkConstructorResult(constructorType, constructorElement);
    }

    protected void checkExplicitConstructorResult(MethodTree tree) {
        // Compare the this value in the constructor's exit store to the declared
        // constructor type.
        PackingClientValue<?> thisValue = atypeFactory.getRegularExitStore(tree).getValue((ThisNode) null);
        Type classType = ((JCTree.JCMethodDecl) tree).sym.owner.type;
        AnnotationMirror declared;
        // Default declared type if no explicit annotation is given
        declared = defaultConstructorQualifier(classType);
        for (AnnotationMirror anno : getConstructorAnnotations(tree)) {
            if (atypeFactory.isSupportedQualifier(anno)) {
                declared = anno;
                break;
            }
        }
        AnnotationMirror top = qualHierarchy.getTopAnnotations().first();

        if (thisValue == null) {
            if (!AnnotationUtils.areSame(top, declared)) {
                checker.reportError(tree, "inconsistent.constructor.type", tree);
            }
        } else {
            AnnotationMirror actual = qualHierarchy.findAnnotationInHierarchy(
                    thisValue.getAnnotations(), atypeFactory.getQualifierHierarchy().getTopAnnotations().first());
            if (!qualHierarchy.isSubtypeQualifiersOnly(actual, declared)) {
                checker.reportError(tree, "inconsistent.constructor.type", tree);
            }
        }
    }

    protected final boolean isParam(Tree expr) {
        if (expr instanceof IdentifierTree) {
            IdentifierTree ident = (IdentifierTree) expr;
            if (ident.getName().toString().equals("this")) {
                return true;
            }

            for (VariableTree param : methodTree.getParameters()) {
                if (param.getName().equals(ident.getName())) {
                    return true;
                }
            }
        } else if (expr instanceof VariableTree) {
            VariableTree var = (VariableTree) expr;
            if (var.getName().toString().equals("this")) {
                return true;
            }

            for (VariableTree param : methodTree.getParameters()) {
                if (param.getName().equals(var.getName())) {
                    return true;
                }
            }
        }

        return false;
    }

    private AnnotationMirrorSet getConstructorAnnotations(MethodTree tree) {
        if (TreeUtils.isConstructor(tree)) {
            com.sun.tools.javac.code.Symbol meth =
                    (com.sun.tools.javac.code.Symbol) TreeUtils.elementFromDeclaration(tree);
            return new AnnotationMirrorSet(
                    meth.getRawTypeAttributes().stream().filter(anno -> anno.position.type.equals(TargetType.METHOD_RETURN))
                            .collect(Collectors.toList()));
        }
        return AnnotationMirrorSet.emptySet();
    }

    protected String getContractPostconditionNotSatisfiedMessage() {
        return "contracts.postcondition.not.satisfied";
    }

    protected void checkDefaultContract(VariableTree param, MethodTree methodTree, PackingClientStore<?, ?> exitStore) {
        JavaExpression paramExpr;
        if (param.getName().contentEquals("this")) {
            paramExpr = new ThisReference(((JCTree) param).type);
        } else {
            paramExpr = JavaExpression.fromVariableTree(param);
        }
        if (!paramsInContract.contains(paramExpr)) {
            Element paramElem = TreeUtils.elementFromDeclaration(param);

            AnnotatedTypeMirror currentType = atypeFactory.getAnnotatedType(param);
            if (exitStore != null) {
                PackingClientValue<?> valueAfterMethod = exitStore.getValue(paramExpr);
                if (valueAfterMethod != null) {
                    currentType.replaceAnnotations(valueAfterMethod.getAnnotations());
                }
            }

            AnnotatedTypeMirror declType = atypeFactory.getAnnotatedTypeLhs(param);

            if (!typeHierarchy.isSubtype(currentType, declType)) {
                checker.reportError(
                        methodTree,
                        getContractPostconditionNotSatisfiedMessage(),
                        methodTree.getName(),
                        contractExpressionAndType(paramElem.toString(), currentType.getAnnotationInHierarchy(atypeFactory.getQualifierHierarchy().getTopAnnotations().first())),
                        contractExpressionAndType(paramElem.toString(), declType.getAnnotationInHierarchy(atypeFactory.getQualifierHierarchy().getTopAnnotations().first())));
            }
        }
    }
}
