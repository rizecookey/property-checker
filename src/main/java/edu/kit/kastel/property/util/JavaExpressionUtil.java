package edu.kit.kastel.property.util;

import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.source.SourceChecker;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

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
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        return new MethodCall(invokedConstructor.getReturnType(), invokedConstructor, null, arguments);
    }

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
        Map<VariableElement, FormalParameter> params = JavaExpression.getFormalParameters(invocation.getElement())
                .stream().collect(Collectors.toMap(FormalParameter::getElement, Function.identity()));
        var methodPath = checker.getTreeUtils().getPath(invocation.getElement());
        JavaExpression receiver = invocation.getReceiver();
        // 1. parse expression in method body scope
        JavaExpression expression = StringToJavaExpression.atPath(stringExpression, methodPath, checker);

        // 2. convert nominal parameter references to FormalParameters
        expression = expression.accept(new JavaExpressionConverter() {
            @Override
            protected JavaExpression visitLocalVariable(LocalVariable localVarExpr, Void unused) {
                return params.get(localVarExpr.getElement());
            }
        }, null);
        // 3. viewpoint adapt to call site
        return viewpointAdapt(expression, receiver, invocation.getArguments());
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
            this.ownerAnno = Objects.requireNonNullElse(exclAnnotation(reference.getReceiver()),
                    exclFactory.MAYBE_ALIASED);
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
            if (expr.getField() != reference.getField()) {
                return false;
            }
            var anno = Objects.requireNonNullElse(exclAnnotation(expr.getReceiver()), exclFactory.READ_ONLY);
            if (AnnotationUtils.areSame(ownerAnno, exclFactory.UNIQUE)) {
                return exclHierarchy.isSubtypeQualifiersOnly(anno, exclFactory.READ_ONLY);
            } else {
                return exclHierarchy.isSubtypeQualifiersOnly(anno, ownerAnno);
            }
        }

        private AnnotationMirror exclAnnotation(JavaExpression expr) {
            var val = store.getValue(expr);
            if (val != null) {
                return exclFactory.getExclusivityAnnotation(val.getAnnotations());
            } else if (expr instanceof MethodCall mc) {
                var methodType = exclFactory.getAnnotatedType(mc.getElement());
                return exclFactory.getExclusivityAnnotation(methodType.getReturnType());
            }
            return null;
        }
    }
}
