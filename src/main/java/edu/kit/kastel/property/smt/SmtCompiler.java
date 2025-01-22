package edu.kit.kastel.property.smt;

import edu.kit.kastel.property.util.UniqueIdMap;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.javacutil.ElementUtils;
import org.sosy_lab.java_smt.api.*;
import org.sosy_lab.java_smt.api.NumeralFormula.IntegerFormula;

import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import java.math.BigInteger;
import java.util.function.Supplier;
import java.util.stream.Stream;

public final class SmtCompiler {

    private final SolverContext context;

    private final UniqueIdMap<Object> unknownValues;
    private final UniqueIdMap<ExecutableElement> functions;
    private final UniqueIdMap<JavaExpression> variables;

    public SmtCompiler(SolverContext context) {
        this.context = context;
        this.unknownValues = new UniqueIdMap<>();
        this.functions = new UniqueIdMap<>();
        this.variables = new UniqueIdMap<>();
    }

    private BooleanFormulaManager bmgr() {
        return context.getFormulaManager().getBooleanFormulaManager();
    }

    private IntegerFormulaManager imgr() {
        return context.getFormulaManager().getIntegerFormulaManager();
    }

    private FloatingPointFormulaManager fpmgr() {
        return context.getFormulaManager().getFloatingPointFormulaManager();
    }

    private UFManager ufmgr() {
        return context.getFormulaManager().getUFManager();
    }

    // TODO move the operations mapping to smtexpression/operators there
    private Formula constructFormula(SmtExpression expression) {
        Formula formula = switch (expression) {
            case SmtExpression.BinaryOperation(var type, var op, var left, var right) -> {
                Supplier<UnsupportedOperationException> unsupported = () -> new UnsupportedOperationException("Unsupported binary operation: " + expression);
                if (left.type().theory() != right.type().theory()) {
                    // we have binary operation between floats and ints. This can happen because
                    // it's allowed in Java, but we can't handle it in SMT (yet)
                    throw unsupported.get();
                }
                final Formula leftF = constructFormula(left);
                final Formula rightF = constructFormula(right);
                yield switch (left.type().theory()) {
                    case INTEGER -> {
                        IntegerFormula iLeftF = (IntegerFormula) leftF;
                        IntegerFormula iRightF = (IntegerFormula) rightF;
                        yield switch (op) {
                            case EQUALS -> imgr().equal(iLeftF, iRightF);
                            case NOT_EQUALS -> bmgr().not(imgr().equal(iLeftF, iRightF));
                            case GREATER -> imgr().greaterThan(iLeftF, iRightF);
                            case GREATER_EQUALS -> imgr().greaterOrEquals(iLeftF, iRightF);
                            case LESS -> imgr().lessThan(iLeftF, iRightF);
                            case LESS_EQUALS -> imgr().lessOrEquals(iLeftF, iRightF);
                            case PLUS -> imgr().add(iLeftF, iRightF);
                            case MINUS -> imgr().subtract(iLeftF, iRightF);
                            case DIVIDE -> jdiv(iLeftF, iRightF);
                            case MULTIPLY -> imgr().multiply(iLeftF, iRightF);
                            case REMAINDER -> jmod(iLeftF, iRightF);
                            default -> throw unsupported.get();
                        };
                    }
                    case FLOATING_POINT -> {
                        FloatingPointFormula fpLeftF = (FloatingPointFormula) leftF;
                        FloatingPointFormula fpRightF = (FloatingPointFormula) rightF;
                        yield switch (op) {
                            case EQUALS -> fpmgr().equalWithFPSemantics(fpLeftF, fpRightF);
                            case NOT_EQUALS -> bmgr().not(fpmgr().equalWithFPSemantics(fpLeftF, fpRightF));
                            case GREATER -> fpmgr().greaterThan(fpLeftF, fpRightF);
                            case GREATER_EQUALS -> fpmgr().greaterOrEquals(fpLeftF, fpRightF);
                            case LESS -> fpmgr().lessThan(fpLeftF, fpRightF);
                            case LESS_EQUALS -> fpmgr().lessOrEquals(fpLeftF, fpRightF);
                            case PLUS -> fpmgr().add(fpLeftF, fpRightF);
                            case MINUS -> fpmgr().subtract(fpLeftF, fpRightF);
                            case DIVIDE -> fpmgr().divide(fpLeftF, fpRightF);
                            case MULTIPLY -> fpmgr().multiply(fpLeftF, fpRightF);
                            default -> throw unsupported.get();
                        };
                    }
                    case BOOLEAN -> {
                        BooleanFormula bLeftF = (BooleanFormula) leftF;
                        BooleanFormula bRightF = (BooleanFormula) rightF;
                        yield switch (op) {
                            case AND, BINARY_AND -> bmgr().and(bLeftF, bRightF);
                            case OR, BINARY_OR -> bmgr().or(bLeftF, bRightF);
                            case EQUALS -> bmgr().equivalence(bLeftF, bRightF);
                            case NOT_EQUALS -> bmgr().not(bmgr().equivalence(bLeftF, bRightF));
                            default -> throw unsupported.get();
                        };

                    }
                    case UNKNOWN -> {
                        // unknown = object type, represented as integers
                        IntegerFormula iLeftF = (IntegerFormula) leftF;
                        IntegerFormula iRightF = (IntegerFormula) rightF;
                        yield switch (op) {
                            case EQUALS -> imgr().equal(iLeftF, iRightF);
                            case NOT_EQUALS -> bmgr().not(imgr().equal(iLeftF, iRightF));
                            default -> throw unsupported.get();
                        };
                    }
                };
            }
            case SmtExpression.FunctionCall call -> {
                var knownFunctionFormula = knownFunction(call);
                yield knownFunctionFormula != null
                        ? knownFunctionFormula
                        : ufmgr().callUF(
                        function(call.underlyingMethod()),
                        call.arguments().stream()
                                .map(this::constructFormula)
                                .toList());
            }
            case SmtExpression.Literal(var type, var value) -> switch (type) {
                case BYTE, SHORT, INT, LONG, CHAR -> imgr().makeNumber(((Number) value).longValue());
                case FLOAT -> fpmgr().makeNumber((double) value, FormulaType.getSinglePrecisionFloatingPointType());
                case DOUBLE -> fpmgr().makeNumber((double) value, FormulaType.getDoublePrecisionFloatingPointType());
                case BOOLEAN -> bmgr().makeBoolean((boolean) value);
                case UNKNOWN -> unknownValue(value);
            };
            case SmtExpression.UnaryOperation(var type, var op, var expr) -> {
                Supplier<UnsupportedOperationException> unsupported =
                        () -> new UnsupportedOperationException("Unsupported unary operation: " + expression);
                var exprF = constructFormula(expr);
                yield switch (type.theory()) {
                    case INTEGER -> switch (op) {
                        case MINUS -> imgr().negate((IntegerFormula) exprF);
                        case PLUS -> exprF;
                        default -> throw unsupported.get();
                    };
                    case FLOATING_POINT -> switch (op) {
                        case MINUS -> fpmgr().negate((FloatingPointFormula) exprF);
                        case PLUS -> exprF;
                        default -> throw unsupported.get();
                    };
                    case BOOLEAN -> switch (op) {
                        case LOGICAL_COMPLEMENT -> bmgr().not((BooleanFormula) exprF);
                        default -> throw unsupported.get();
                    };
                    case UNKNOWN -> throw unsupported.get();
                };
            }
            case SmtExpression.Variable variable -> variable(variable.expression());
        };

        return expression.type().theory() == SmtType.Theory.INTEGER
                ? withOverflow((IntegerFormula) formula, expression.type())
                : formula;
    }

    // integer division with java semantics
    private IntegerFormula jdiv(IntegerFormula a, IntegerFormula b) {
        var q = imgr().divide(a, b);
        return bmgr().ifThenElse(
                bmgr().and(
                        imgr().lessThan(imgr().multiply(a, b), imgr().makeNumber(0)),
                        bmgr().not(imgr().equal(a, imgr().multiply(b, imgr().add(q, imgr().makeNumber(1)))))
                ),
                imgr().add(q, imgr().makeNumber(1)),
                q
        );
    }

    // modulo with java semantics
    private IntegerFormula jmod(IntegerFormula a, IntegerFormula b) {
        var r = imgr().modulo(a, b);
        return bmgr().ifThenElse(
                bmgr().and(
                        imgr().lessThan(imgr().multiply(a, b), imgr().makeNumber(0)),
                        bmgr().not(imgr().equal(imgr().makeNumber(0), imgr().subtract(r, b)))
                ),
                imgr().subtract(r, b),
                r
        );
    }

    private Formula knownFunction(SmtExpression.FunctionCall functionCall) {
        return switch (ElementUtils.getQualifiedName(functionCall.underlyingMethod())) {
            case "java.lang.Math.floorMod(int,int)",
                 "java.lang.Math.floorMod(long,int)",
                 "java.lang.Math.floorMod(long,long)" -> imgr().modulo(
                    (IntegerFormula) constructFormula(functionCall.arguments().get(0)),
                    (IntegerFormula) constructFormula(functionCall.arguments().get(1))
            );
            case "java.lang.Math.floorDiv(int,int)",
                 "java.lang.Math.floorDiv(long,int)",
                 "java.lang.Math.floorDiv(long,long)" -> imgr().divide(
                    (IntegerFormula) constructFormula(functionCall.arguments().get(0)),
                    (IntegerFormula) constructFormula(functionCall.arguments().get(1))
            );
            default -> null;
        };
    }

    private IntegerFormula withOverflow(IntegerFormula formula, SmtType type) {
        int bits = switch (type) {
            case BYTE -> Byte.SIZE;
            case SHORT -> Short.SIZE;
            case INT -> Integer.SIZE;
            case LONG -> Long.SIZE;
            case CHAR -> Character.SIZE;
            default -> throw new AssertionError(type + " is not an integer type");
        };

        var mgr = context.getFormulaManager().getIntegerFormulaManager();
        IntegerFormula offset = mgr.makeNumber(BigInteger.ONE.shiftLeft(bits - 1));
        IntegerFormula modulus = mgr.makeNumber(BigInteger.ONE.shiftLeft(bits));
        // below code constructs formula equivalent to the expression:
        // (Math.floorMod(formula + offset, modulus) - offset
        // this converts any integer to be in the correct value space.
        // for characters, there is no offset (they are unsigned)
        if (type != SmtType.CHAR) {
            formula = mgr.add(formula, offset);
        }
        formula = mgr.modulo(formula, modulus);
        if (type != SmtType.CHAR) {
            formula = mgr.subtract(formula, offset);
        }
        return formula;
    }

    private Formula variable(JavaExpression expr) {
        String variableName = "v_" + variables.getId(expr);
        SmtType type = SmtType.fromTypeMirror(expr.getType());
        return type == SmtType.UNKNOWN
                ? unknownValue(expr)
                : context.getFormulaManager().makeVariable(formulaType(type), variableName);
    }

    private FunctionDeclaration<?> function(ExecutableElement method) {
        String functionName = "f_" + functions.getId(method);
        Stream<SmtType> paramTypes = method.getParameters().stream()
                .map(VariableElement::asType)
                .map(SmtType::fromTypeMirror);
        if (!ElementUtils.isStatic(method)) {
            paramTypes = Stream.concat(Stream.of(SmtType.UNKNOWN), paramTypes);
        }
        return ufmgr().declareUF(
                functionName,
                formulaType(SmtType.fromTypeMirror(method.getReturnType())),
                paramTypes.map(this::formulaType).toArray(FormulaType<?>[]::new)
        );
    }

    // represent a value of unknown type (literal value or expression) in SMT by assigning it an integer value
    private IntegerFormula unknownValue(Object value) {
        return imgr().makeNumber(unknownValues.getId(value));
    }

    private FormulaType<?> formulaType(SmtType type) {
        return switch (type) {
            case BYTE, SHORT, INT, LONG, CHAR -> FormulaType.IntegerType;
            case FLOAT -> FormulaType.getSinglePrecisionFloatingPointType();
            case DOUBLE -> FormulaType.getDoublePrecisionFloatingPointType();
            case BOOLEAN -> FormulaType.BooleanType;
            // Unknown means some declared type (object).
            // We can represent such values in SMT by assigning them an integer identity
            case UNKNOWN -> FormulaType.IntegerType;
        };
    }
    
    public Formula compile(SmtExpression expression) {
        return constructFormula(expression);
    }
}
