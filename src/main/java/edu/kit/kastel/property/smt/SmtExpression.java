package edu.kit.kastel.property.smt;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import org.checkerframework.com.google.common.base.Verify;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.javacutil.ElementUtils;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import java.util.List;
import java.util.Objects;
import java.util.stream.Collectors;

// One SmtExpression <=> JavaExpression
public sealed interface SmtExpression {

    SmtType type();

    // expr is either local variable or field access
    // expressions are not really needed, just something to make the variable unique per expression - string?
    record Variable(SmtType type, JavaExpression expression) implements SmtExpression {

        public Variable {
            Verify.verify(expression instanceof LocalVariable
                    || expression instanceof FieldAccess
                    || expression instanceof ThisReference);
        }

        @Override
        public String toString() {
            return expression.toString();
        }
    }

    record FunctionCall(SmtType type, List<SmtExpression> arguments, ExecutableElement underlyingMethod) implements SmtExpression {

        @Override
        public String toString() {
            String prefix;
            List<SmtExpression> args = arguments;
            if (ElementUtils.isStatic(underlyingMethod)) {
                prefix = ElementUtils.getQualifiedName(underlyingMethod.getEnclosingElement())
                        + "." + underlyingMethod.getSimpleName();
            } else if (underlyingMethod.getKind() == ElementKind.CONSTRUCTOR) {
                prefix = "new " + ElementUtils.getQualifiedName(underlyingMethod.getEnclosingElement());
            } else {
                prefix = arguments.getFirst() + "." + underlyingMethod.getSimpleName();
                args = args.subList(1, args.size());
            }

            return prefix + args.stream().map(Object::toString).collect(Collectors.joining(", ", "(", ")"));
        }
    }

    record Literal(SmtType type, Object value) implements SmtExpression {
        @Override
        public String toString() {
            return Objects.toString(value);
        }
    }

    record BinaryOperation(SmtType type, BinaryExpr.Operator operator, SmtExpression left, SmtExpression right) implements SmtExpression {
        @Override
        public String toString() {
            return "(" + left + " " + operator.asString() + " " + right + ")";
        }
    }

    record UnaryOperation(SmtType type, UnaryExpr.Operator operator, SmtExpression expression) implements SmtExpression {
        @Override
        public String toString() {
            return operator.asString() + "(" + expression + ")";
        }
    }

}
