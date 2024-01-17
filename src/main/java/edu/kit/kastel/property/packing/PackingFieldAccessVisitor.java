package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationFieldAccessAbstractVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFValue;

public class PackingFieldAccessVisitor extends InitializationFieldAccessAbstractVisitor<
        CFValue, PackingStore, PackingTransfer, PackingAnalysis, PackingFieldAccessAnnotatedTypeFactory> {

    public PackingFieldAccessVisitor(BaseTypeChecker checker) {
        super(checker);
    }
}
