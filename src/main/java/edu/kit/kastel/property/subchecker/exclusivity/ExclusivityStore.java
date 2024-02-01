package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.JavaExpression;
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
}
