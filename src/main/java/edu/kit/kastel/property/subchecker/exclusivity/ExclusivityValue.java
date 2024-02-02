package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;

public class ExclusivityValue extends CFAbstractValue<ExclusivityValue> {

    /**
     * Creates a new CFAbstractValue.
     *
     * @param analysis       the analysis class this value belongs to
     * @param annotations    the annotations in this abstract value
     * @param underlyingType the underlying (Java) type in this abstract value
     */
    public ExclusivityValue(ExclusivityAnalysis analysis, AnnotationMirrorSet annotations, TypeMirror underlyingType) {
        super(analysis, annotations, underlyingType);
    }
}
