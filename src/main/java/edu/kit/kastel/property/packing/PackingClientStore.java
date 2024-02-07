package edu.kit.kastel.property.packing;

import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;

public abstract class PackingClientStore<V extends CFAbstractValue<V>, S extends CFAbstractStore<V, S>>
        extends CFAbstractStore<V, S> {

    protected PackingClientStore(CFAbstractAnalysis<V, S, ?> analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    protected PackingClientStore(CFAbstractStore<V, S> other) {
        super(other);
    }

    @Override
    public void insertValue(
            JavaExpression expr, @Nullable V value, boolean permitNondeterministic) {
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
    public @Nullable V getValue(JavaExpression expr) {
        if (expr instanceof ThisReference || (expr instanceof LocalVariable && expr.toString().equals("this"))) {
            return thisValue;
        }
        return super.getValue(expr);
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
