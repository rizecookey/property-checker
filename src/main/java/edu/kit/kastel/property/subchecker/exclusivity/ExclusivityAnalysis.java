package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;

public class ExclusivityAnalysis extends CFAbstractAnalysis<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> {

    public ExclusivityAnalysis(
            BaseTypeChecker checker,
            ExclusivityAnnotatedTypeFactory factory) {
        super(checker, factory);
    }

    @Override
    public ExclusivityStore createEmptyStore(boolean sequentialSemantics) {
        return new ExclusivityStore(this, sequentialSemantics);
    }

    @Override
    public ExclusivityStore createCopiedStore(ExclusivityStore s) {
        return new ExclusivityStore(s);
    }

    @Override
    public ExclusivityValue createAbstractValue(AnnotationMirrorSet annotations, TypeMirror underlyingType) {
        if (!CFAbstractValue.validateSet(annotations, underlyingType, atypeFactory)) {
            return null;
        }
        return new ExclusivityValue(this, annotations, underlyingType);
    }
}
