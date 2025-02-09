package edu.kit.kastel.property.util;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.source.SourceChecker;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.Map;
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

    /**
     * Construct a pseudo method invocation from a constructor call tree that can be used to represent constructor calls
     * as a {@code JavaExpression} (where they are otherwise unsupported).
     * <p>
     * The resulting method call uses:
     * <ul>
     *     <li>the underlying constructor as its {@code ExecutableElement}</li>
     *     <li>a {@code ClassName} as the receiver</li>
     *     <li>the constructed class type as its return type</li>
     *     <li>the arguments as-is (converted to {@code JavaExpression}s)</li>
     * </ul>
     * <p>
     * Note that this method only creates such a pseudo-call for the given {@code NewClassTree}, not
     * for any {@code NewClassTree}s that are potentially nested in the arguments.
     * Thus, the resulting expression may contain {@code Unknown}s.
     *
     * @param tree the constructor invocation tree
     * @return a method call expression representing the constructor call
     */
    public static MethodCall constructorCall(NewClassTree tree) {
        ExecutableElement invokedConstructor = TreeUtils.elementFromUse(tree);
        TypeMirror type = invokedConstructor.getEnclosingElement().asType();
        var arguments = tree.getArguments().stream().map(JavaExpression::fromTree).toList();
        return new MethodCall(type, invokedConstructor,
                new ClassName(type), arguments);
    }


    /**
     * Parses an expression "at the callsite" of a method invocation,
     * meaning that the expression is first parsed with the parameter variables and `this` in the scope of the
     * method declaration and then viewpoint-adapted to the invocation.
     * <p>
     * For example, the expression {@code a < this.f} at the invocation {@code b.foo(x + y)},
     * where {@code foo} is declared as {@code void foo(int a)}, would result in {@code (x + y) < b.f} being parsed.
     *
     * @param stringExpression The expression to parse, referencing `this` and method parameters by name.
     * @param invocation The method invocation to viewpoint-adapt to.
     * @param checker The source checker being used
     * @return a viewpoint-adapted {@code JavaExpression}
     * @throws JavaExpressionParseUtil.JavaExpressionParseException if there is a parsing error
     */
    public static JavaExpression parseAtCallsite(String stringExpression, MethodCall invocation, SourceChecker checker)
            throws JavaExpressionParseUtil.JavaExpressionParseException {

        TreePath methodPath = checker.getTreeUtils().getPath(invocation.getElement());
        JavaExpression receiver = invocation.getReceiver();

        ClassTree classTree = TreePathUtil.enclosingClass(methodPath);
        // FIXME: bug in checker framework or compiler (?!): `type` field of classTree is sometimes null,
        //  which breaks checker framework. This is a very bad, not good hack to make sure it is set.
        //  (bug can be demonstrated on the CaseStudyMutable test case)
        ((JCTree) classTree).setType((Type) TreeUtils.elementFromDeclaration(classTree).asType());

        // 1. parse expression in method body scope
        JavaExpression expression = StringToJavaExpression.atPath(stringExpression, methodPath, checker);
        // 2. convert nominal parameter references to FormalParameters
        expression = convertParams(expression, invocation.getElement());
        // 3. viewpoint adapt to call site
        return viewpointAdapt(expression, receiver instanceof ClassName ? null : receiver, invocation.getArguments());
    }

    /**
     * Converts all nominal parameter references in an expression (i.e. {@code LocalVariable}s)
     * to {@code FormalParameter}s according to the parameters declared by the given method element.
     *
     * @param expression The expression to convert
     * @param element The {@code ExecutableElement} providing parameter information
     * @return {@code expression}, with formal (enumerated) parameters instead of local variables
     */
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

    /**
     * Tests whether a given {@code JavaExpression} could depend on the value of a specific field.
     * "Could depend" means that the JavaExpression either references the exact same field or references the same field
     * on a different expression that could be an alias of the dependency. Whether two expressions can be
     * aliases is determined by the exclusivity type system.
     * <p>
     * {@code expr} is also considered dependent if it contains any method call, since we have no way of knowing
     * whether the called method uses the field in its implementation somehow.
     *
     * @param expr The expression to test.
     * @param dependency The field access to look for in {@code expr}.
     * @param tree the position in the code where this test is performed. This is relevant for the exclusivity analysis.
     * @param exclFactory the exclusivity factory
     * @return {@code true} if {@code expr} should be considered dependent on {@code dependency}.
     */
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
