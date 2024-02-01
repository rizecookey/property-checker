package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.ClassName;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFValue;

import javax.lang.model.element.Element;

public class PackingStore extends InitializationAbstractStore<CFValue, PackingStore> {

    public PackingStore(PackingAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    public PackingStore(PackingStore other) {
        super(other);
    }

    @Override
    public void insertValue(
            JavaExpression expr, @Nullable CFValue value, boolean permitNondeterministic) {
        if (!shouldInsert(expr, value, permitNondeterministic)) {
            return;
        }

        computeNewValueAndInsert(
                expr,
                value,
                (old, newValue) -> newValue,
                permitNondeterministic);

        if (expr instanceof FieldAccess) {
            FieldAccess fa = (FieldAccess) expr;
            if (fa.getReceiver() instanceof ThisReference
                    || fa.getReceiver() instanceof ClassName) {
                addInitializedField(fa.getField());
            }
        }
    }

    @Override
    public boolean isFieldInitialized(Element f) {
        // We don't use the fbc commitment mechanism.
        return false;
    }
}
