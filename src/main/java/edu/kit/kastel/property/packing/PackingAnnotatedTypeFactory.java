package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationChecker;
import org.checkerframework.checker.initialization.InitializationFieldAccessAbstractAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationFieldAccessSubchecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;

public class PackingAnnotatedTypeFactory
        extends InitializationAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    public PackingAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected @Nullable PackingFieldAccessAnnotatedTypeFactory getFieldAccessFactory() {
        PackingChecker checker = getChecker();
        BaseTypeChecker targetChecker = checker.getSubchecker(checker.getTargetCheckerClass());
        return targetChecker.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }

    @Override
    public PackingChecker getChecker() {
        return (PackingChecker) super.getChecker();
    }
}
