package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationFieldAccessAbstractAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;

public class PackingFieldAccessAnnotatedTypeFactory
        extends InitializationFieldAccessAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    public PackingFieldAccessAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected PackingAnalysis createFlowAnalysis() {
        return new PackingAnalysis(checker, this);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(
            CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }
}
