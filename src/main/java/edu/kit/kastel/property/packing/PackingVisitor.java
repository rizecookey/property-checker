package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFValue;

public class PackingVisitor
        extends InitializationAbstractVisitor<CFValue, PackingStore, PackingTransfer, PackingAnalysis, PackingAnnotatedTypeFactory> {

    public PackingVisitor(BaseTypeChecker checker) {
        super(checker);
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        // Don't load the factory reflexively based on checker class name.
        // Instead, always use the PackingAnnotatedTypeFactory.
        return new PackingAnnotatedTypeFactory(checker);
    }
}
