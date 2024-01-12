package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationStore;
import org.checkerframework.checker.initialization.InitializationTransfer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.framework.flow.CFValue;

public class PackingAnnotatedTypeFactory extends InitializationAnnotatedTypeFactory {

    public PackingAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
    }

    @Override
    protected @Nullable CFGVisualizer<CFValue, PackingStore, PackingTransfer> createCFGVisualizer() {
        return super.createCFGVisualizer();
    }
}
