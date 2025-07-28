package edu.kit.kastel.property.packing;

import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.type.TypeMirror;

public abstract class PackingClientValue<V extends PackingClientValue<V>> extends CFAbstractValue<V> {


    protected PackingClientValue(CFAbstractAnalysis<V, ?, ?> analysis, AnnotationMirrorSet annotations, TypeMirror underlyingType) {
        super(analysis, annotations, underlyingType);
    }
}
