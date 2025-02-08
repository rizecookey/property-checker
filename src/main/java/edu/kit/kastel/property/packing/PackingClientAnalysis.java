package edu.kit.kastel.property.packing;

import com.sun.source.tree.Tree;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

public abstract class PackingClientAnalysis<
        V extends PackingClientValue<V>,
        S extends PackingClientStore<V, S>,
        T extends PackingClientTransfer<V, S, T>>
        extends CFAbstractAnalysis<V, S, T>  {

    // current position tracker. This _looks_ like a duplicate of currentTree or currentNode at first, but those are
    // not suitable replacements as they have other internal uses that are incompatible with what we need this value for.
    private Tree position = null;

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

    // TODO: check if there can be ambiguities here (subtle bugs when refinement is parsed in the wrong place)
    /**
     * Returns the tree currently set to be the context for parsing refinement expressions.
     * This must be set and kept up to date by PackingClientTransfer and its sub classes via {@link #setPosition(Tree)}.
     *
     * @return A {@code Tree}.
     */
    @Nullable
    public Tree getPosition() {
        return position;
    }

    public void setPosition(@Nullable  Tree position) {
        this.position = position;
    }

}
