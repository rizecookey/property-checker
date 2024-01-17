package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.*;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;

public class PackingAnalysis extends InitializationAbstractAnalysis<CFValue, PackingStore, PackingTransfer> {

    protected PackingAnalysis(
            BaseTypeChecker checker,
            InitializationParentAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> factory) {
        super(checker, factory);
    }

    @Override
    public PackingStore createEmptyStore(boolean seqentialSemantics) {
        return new PackingStore(this, seqentialSemantics);
    }

    @Override
    public PackingStore createCopiedStore(PackingStore s) {
        return new PackingStore(s);
    }

    @Override
    public @Nullable CFValue createAbstractValue(AnnotationMirrorSet annotations, TypeMirror underlyingType) {
        return defaultCreateAbstractValue(this, annotations, underlyingType);
    }

    @Override
    @SuppressWarnings("unchecked")
    public InitializationParentAnnotatedTypeFactory<
            CFValue, PackingStore, PackingTransfer, PackingAnalysis>
    getTypeFactory() {
        return (InitializationParentAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis>)
                super.getTypeFactory();
    }
}
