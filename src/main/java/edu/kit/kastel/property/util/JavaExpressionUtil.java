package edu.kit.kastel.property.util;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityViewpointAdapter;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.source.SourceChecker;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.checkerframework.dataflow.expression.ViewpointAdaptJavaExpression.viewpointAdapt;

public class JavaExpressionUtil {

    public static JavaExpression getReceiver(JavaExpression expr) {
        return switch (expr) {
            case MethodCall m -> m.getReceiver();
            case FieldAccess f -> f.getReceiver();
            default -> null;
        };
    }

    public static MethodCall constructorCall(NewClassTree tree) {
        ExecutableElement invokedConstructor = TreeUtils.elementFromUse(tree);
        TypeMirror type = invokedConstructor.getEnclosingElement().asType();
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        return new MethodCall(type, invokedConstructor,
                new ClassName(type), arguments);
    }

    // TODO: why does this exist? JavaExpression.fromTree is already a thing
    public static MethodCall methodCall(MethodInvocationTree tree) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(tree);
        JavaExpression receiver = null;
        var receiverTree = TreeUtils.getReceiverTree(tree);
        if (receiverTree == null) {
            // no explicit receiver
            if (ElementUtils.isStatic(invokedMethod)) {
                // static method => class is the receiver
                receiver = new ClassName(invokedMethod.getEnclosingElement().asType());
            } else if (invokedMethod.getReceiverType() != null) {
                // instance method => `this` is the receiver
                receiver = new ThisReference(invokedMethod.getReceiverType());
            }
        } else {
            // explicit receiver
            receiver = JavaExpression.fromTree(receiverTree);
        }
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        return new MethodCall(invokedMethod.getReturnType(), invokedMethod, receiver, arguments);
    }

    public static JavaExpression parseAtCallsite(String stringExpression, MethodCall invocation, SourceChecker checker)
            throws JavaExpressionParseUtil.JavaExpressionParseException {

        TreePath methodPath = checker.getTreeUtils().getPath(invocation.getElement());
        JavaExpression receiver = invocation.getReceiver();

        // 1. parse expression in method body scope

        ClassTree classTree = TreePathUtil.enclosingClass(methodPath);
        // FIXME: bug in checker framework or compiler (?!): `type` field of classTree is sometimes null,
        //  which breaks checker framework. This is a very bad, not good hack to make sure it is set.
        //  (bug can be demonstrated on the CaseStudyMutable test case)
        ((JCTree) classTree).setType((Type) TreeUtils.elementFromDeclaration(classTree).asType());
        JavaExpression expression = StringToJavaExpression.atPath(stringExpression, methodPath, checker);

        // 2. convert nominal parameter references to FormalParameters
        expression = convertParams(expression, invocation.getElement());
        // 3. viewpoint adapt to call site
        return viewpointAdapt(expression, receiver, invocation.getArguments());
    }

    public static JavaExpression convertParams(JavaExpression expression, ExecutableElement element) {
        Map<VariableElement, FormalParameter> params = JavaExpression.getFormalParameters(element)
                .stream().collect(Collectors.toMap(FormalParameter::getElement, Function.identity()));
        return expression.accept(new JavaExpressionConverter() {
            @Override
            protected JavaExpression visitLocalVariable(LocalVariable localVarExpr, Void unused) {
                return params.get(localVarExpr.getElement());
            }
        }, null);
    }

    public static boolean maybeDependent(
            JavaExpression expr,
            FieldAccess dependency,
            Tree tree,
            ExclusivityAnnotatedTypeFactory exclFactory
    ) {
        var scanner = new AliasScanner(exclFactory, tree, dependency);
        scanner.scan(expr, null);
        return scanner.found;
    }

    private static class AliasScanner extends JavaExpressionScanner<Void> {

        final ExclusivityStore store;
        final FieldAccess reference;
        final QualifierHierarchy exclHierarchy;
        final ExclusivityAnnotatedTypeFactory exclFactory;
        final AnnotationMirror ownerAnno;

        boolean found = false;

        AliasScanner(ExclusivityAnnotatedTypeFactory exclFactory, Tree tree, FieldAccess reference) {
            this.store = exclFactory.getStoreBefore(tree);
            this.reference = reference;
            this.exclFactory = exclFactory;
            this.exclHierarchy = exclFactory.getQualifierHierarchy();
            this.ownerAnno = store.deriveExclusivityValue(reference);
        }

        @Override
        protected Void visitFieldAccess(FieldAccess fieldAccessExpr, Void unused) {
            // could the visited FieldAccess point to the input field on the same object?
            if (possibleAlias(fieldAccessExpr)) {
                found = true;
                return null;
            }

            return super.visitFieldAccess(fieldAccessExpr, unused);
        }

        @Override
        protected Void visitMethodCall(MethodCall methodCallExpr, Void unused) {
            // TODO: add "known" exceptions here for methods that are actually "pure" (no dependency on fields)
            // if a method is called, we conservatively assume that the method implementation depends on the
            // value of the input field behind an owner alias somehow, and thus we consider it dependent.
            found = true;
            return null;
        }

        private boolean possibleAlias(FieldAccess expr) {
            if (expr.equals(reference)) {
                return true;
            }

            if (expr.getField() != reference.getField()) {
                return false;
            }


            var anno = store.deriveExclusivityValue(expr);
            if (AnnotationUtils.areSame(ownerAnno, exclFactory.UNIQUE)) {
                return exclHierarchy.isSubtypeQualifiersOnly(exclFactory.READ_ONLY, anno);
            } else {
                return exclHierarchy.isSubtypeQualifiersOnly(anno, ownerAnno);
            }
        }
    }
}
