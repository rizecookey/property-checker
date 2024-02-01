package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractStore;

public class ExclusivityStore extends CFAbstractStore<ExclusivityValue, ExclusivityStore> {

    protected ExclusivityStore(ExclusivityAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    protected ExclusivityStore(ExclusivityStore other) {
        super(other);
    }

    @Override
    public void insertValue(
            JavaExpression expr, @Nullable ExclusivityValue value, boolean permitNondeterministic) {
        if (!shouldInsert(expr, value, permitNondeterministic)) {
            return;
        }

        computeNewValueAndInsert(
                expr,
                value,
                (old, newValue) -> newValue,
                permitNondeterministic);
    }

    @Override
    protected boolean shouldInsert(JavaExpression expr, @Nullable ExclusivityValue value, boolean permitNondeterministic) {
        if (!canInsertJavaExpression(expr)) {
            return false;
        }

        ExclusivityAnnotatedTypeFactory factory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory();
        ExclusivityValue oldValue = getValue(expr);

        return super.shouldInsert(expr, value, permitNondeterministic) &&
                (oldValue == null || !factory.getQualifierHierarchy().isSubtypeQualifiersOnly(
                factory.getExclusivityAnnotation(getValue(expr).getAnnotations()),
                factory.EXCL_BOTTOM));
    }

    @Override
    public void clearValue(JavaExpression expr) {
        if (expr instanceof ThisReference) {
            thisValue = null;
        } else {
            super.clearValue(expr);
        }
    }
}
