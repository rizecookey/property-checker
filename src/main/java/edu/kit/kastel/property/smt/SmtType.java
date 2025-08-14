package edu.kit.kastel.property.smt;

import org.checkerframework.dataflow.expression.JavaExpression;

import javax.lang.model.type.PrimitiveType;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.TypeKindVisitor14;

public enum SmtType {

    BYTE(Theory.INTEGER),
    SHORT(Theory.INTEGER),
    INT(Theory.INTEGER),
    LONG(Theory.INTEGER),
    FLOAT(Theory.FLOATING_POINT),
    DOUBLE(Theory.FLOATING_POINT),
    CHAR(Theory.INTEGER),
    BOOLEAN(Theory.BOOLEAN),
    // unrepresentable types - can appear as function arguments, but don't have operations
    UNKNOWN(Theory.UNKNOWN);

    private final Theory theory;

    SmtType(Theory theory) {
        this.theory = theory;
    }

    public Theory theory() {
        return theory;
    }

    // TODO: this might be a duplicate of the existing FormulaType concept
    public enum Theory {
        INTEGER,
        FLOATING_POINT,
        BOOLEAN,
        UNKNOWN;
    }

    public static SmtType fromExpression(JavaExpression expression) {
        return fromTypeMirror(expression.getType());
    }

    public static SmtType fromTypeMirror(TypeMirror type) {
        SmtType sType = type.accept(new TypeKindVisitor14<SmtType, Void>() {
            @Override
            public SmtType visitPrimitiveAsInt(PrimitiveType t, Void unused) {
                return INT;
            }

            @Override
            public SmtType visitPrimitiveAsByte(PrimitiveType t, Void unused) {
                return BYTE;
            }

            @Override
            public SmtType visitPrimitiveAsBoolean(PrimitiveType t, Void unused) {
                return BOOLEAN;
            }

            @Override
            public SmtType visitPrimitiveAsShort(PrimitiveType t, Void unused) {
                return SHORT;
            }

            @Override
            public SmtType visitPrimitiveAsLong(PrimitiveType t, Void unused) {
                return LONG;
            }

            @Override
            public SmtType visitPrimitiveAsChar(PrimitiveType t, Void unused) {
                return CHAR;
            }

            @Override
            public SmtType visitPrimitiveAsFloat(PrimitiveType t, Void unused) {
                return FLOAT;
            }

            @Override
            public SmtType visitPrimitiveAsDouble(PrimitiveType t, Void unused) {
                return DOUBLE;
            }

        }, null);
        return sType == null ? UNKNOWN : sType;
    }

}
