package edu.kit.kastel.property.subchecker.exclusivity;

import edu.kit.kastel.property.packing.PackingClientValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;

public class ExclusivityValue extends PackingClientValue<ExclusivityValue> {

    public ExclusivityValue(ExclusivityAnalysis analysis, AnnotationMirrorSet annotations, TypeMirror underlyingType) {
        super(analysis, annotations, underlyingType);
    }
}
