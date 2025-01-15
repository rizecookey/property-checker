package edu.kit.kastel.property.smt;

import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import org.checkerframework.dataflow.expression.*;

import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.stream.Stream;

// converts JavaExpression -> SmtExpression and collects all java references (field accesses and underlyingMethod calls) made on the way as well
// things not representable in SMT -> stub variables (unknown type)
public class JavaToSmtExpression extends JavaExpressionVisitor<SmtExpression, Set<JavaExpression>> {

    @Override
    protected SmtExpression visitArrayAccess(ArrayAccess arrayAccessExpr, Set<JavaExpression> refs) {
        throw new UnsupportedOperationException("No array support yet");
    }

    @Override
    protected SmtExpression visitArrayCreation(ArrayCreation arrayCreationExpr, Set<JavaExpression> refs) {
        throw new UnsupportedOperationException("impure operation (array creation)");
    }

    @Override
    protected SmtExpression visitClassName(ClassName classNameExpr, Set<JavaExpression> refs) {
        throw new UnsupportedOperationException("Don't known what to do with class name " + classNameExpr);
    }

    @Override
    protected SmtExpression visitUnknown(Unknown unknownExpr, Set<JavaExpression> refs) {
        throw new UnsupportedOperationException("Missing checker framework support for expression " + unknownExpr);
    }

    @Override
    protected SmtExpression visitFormalParameter(FormalParameter parameterExpr, Set<JavaExpression> refs) {
        refs.add(parameterExpr);
        return new SmtExpression.Variable(SmtType.fromExpression(parameterExpr), parameterExpr);
    }

    @Override
    protected SmtExpression visitLocalVariable(LocalVariable localVarExpr, Set<JavaExpression> refs) {
        refs.add(localVarExpr);
        return new SmtExpression.Variable(SmtType.fromExpression(localVarExpr), localVarExpr);
    }

    @Override
    protected SmtExpression visitThisReference(ThisReference thisExpr, Set<JavaExpression> refs) {
        refs.add(thisExpr);
        return new SmtExpression.Variable(SmtType.fromExpression(thisExpr), thisExpr);
    }

    @Override
    protected SmtExpression visitUnaryOperation(UnaryOperation unaryOpExpr, Set<JavaExpression> refs) {
        SmtExpression expr = visit(unaryOpExpr.getOperand(), refs);
        UnaryExpr.Operator op = switch (unaryOpExpr.getOperationKind()) {
            case UNARY_MINUS -> UnaryExpr.Operator.MINUS;
            case LOGICAL_COMPLEMENT -> UnaryExpr.Operator.LOGICAL_COMPLEMENT;
            default -> throw new UnsupportedOperationException("Don't know how to handle unary operator " + unaryOpExpr.getOperationKind());
        };
        return new SmtExpression.UnaryOperation(SmtType.fromExpression(unaryOpExpr), op, expr);
    }

    @Override
    protected SmtExpression visitBinaryOperation(BinaryOperation binaryOpExpr, Set<JavaExpression> refs) {
        SmtExpression left = visit(binaryOpExpr.getLeft(), refs);
        SmtExpression right = visit(binaryOpExpr.getRight(), refs);

        BinaryExpr.Operator op = switch (binaryOpExpr.getOperationKind()) {
            case AND, CONDITIONAL_AND -> BinaryExpr.Operator.AND;
            case OR, CONDITIONAL_OR -> BinaryExpr.Operator.OR;
            case PLUS -> BinaryExpr.Operator.PLUS;
            case MINUS -> BinaryExpr.Operator.MINUS;
            case DIVIDE -> BinaryExpr.Operator.DIVIDE;
            case MULTIPLY -> BinaryExpr.Operator.MULTIPLY;
            case REMAINDER -> BinaryExpr.Operator.REMAINDER;
            case LESS_THAN -> BinaryExpr.Operator.LESS;
            case LESS_THAN_EQUAL -> BinaryExpr.Operator.LESS_EQUALS;
            case GREATER_THAN -> BinaryExpr.Operator.GREATER;
            case GREATER_THAN_EQUAL -> BinaryExpr.Operator.GREATER_EQUALS;
            case NOT_EQUAL_TO -> BinaryExpr.Operator.NOT_EQUALS;
            case EQUAL_TO -> BinaryExpr.Operator.EQUALS;
            default -> throw new UnsupportedOperationException("Don't know how to handle binary operator " + binaryOpExpr.getOperationKind());
        };
        return new SmtExpression.BinaryOperation(SmtType.fromExpression(binaryOpExpr), op, left, right);
    }

    @Override
    protected SmtExpression visitValueLiteral(ValueLiteral literalExpr, Set<JavaExpression> refs) {
        return new SmtExpression.Literal(SmtType.fromExpression(literalExpr), literalExpr.getValue());
    }

    @Override
    protected SmtExpression visitFieldAccess(FieldAccess fieldAccessExpr, Set<JavaExpression> refs) {
        refs.add(fieldAccessExpr);
        return new SmtExpression.Variable(SmtType.fromExpression(fieldAccessExpr), fieldAccessExpr);
    }

    @Override
    protected SmtExpression visitMethodCall(MethodCall methodCallExpr, Set<JavaExpression> refs) {
        refs.add(methodCallExpr);
        JavaExpression receiver = methodCallExpr.getReceiver();
        Stream<JavaExpression> argStream = methodCallExpr.getArguments().stream();
        if (!(receiver instanceof ClassName)) {
            argStream = Stream.concat(Stream.of(receiver), argStream);
        }
        List<SmtExpression> args = argStream.map(arg -> visit(arg, refs)).toList();

        SmtType returnType = SmtType.fromTypeMirror(methodCallExpr.getType());
        return new SmtExpression.FunctionCall(returnType, args, methodCallExpr.getElement());
    }

    public static Result convert(JavaExpression expression) {
        Set<JavaExpression> refs = new HashSet<>();
        SmtExpression smt = expression.accept(new JavaToSmtExpression(), refs);
        return new Result(smt, refs);
    }

    public record Result(SmtExpression smt, Set<JavaExpression> references) {}

}
