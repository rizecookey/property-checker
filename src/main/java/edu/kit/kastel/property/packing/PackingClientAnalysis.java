package edu.kit.kastel.property.packing;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

public abstract class PackingClientAnalysis<
        V extends PackingClientValue<V>,
        S extends PackingClientStore<V, S>,
        T extends PackingClientTransfer<V, S, T>>
        extends CFAbstractAnalysis<V, S, T>  {

    protected PackingClientAnalysis(BaseTypeChecker checker, GenericAnnotatedTypeFactory<V, S, T, ? extends CFAbstractAnalysis<V, S, T>> factory, int maxCountBeforeWidening) {
        super(checker, factory, maxCountBeforeWidening);
    }

    protected PackingClientAnalysis(BaseTypeChecker checker, GenericAnnotatedTypeFactory<V, S, T, ? extends CFAbstractAnalysis<V, S, T>> factory) {
        super(checker, factory);
    }

    @Override
    public PackingClientAnnotatedTypeFactory<V, S, T, ? extends CFAbstractAnalysis<V, S, T>> getTypeFactory() {
        return (PackingClientAnnotatedTypeFactory<V, S, T, ? extends CFAbstractAnalysis<V, S, T>>) super.getTypeFactory();
    }
}
