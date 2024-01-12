package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationFieldAccessTreeAnnotator;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

public class PackingFieldAccessTreeAnnotator extends InitializationFieldAccessTreeAnnotator {

    public PackingFieldAccessTreeAnnotator(GenericAnnotatedTypeFactory<?, ?, ?, ?> atypeFactory) {
        super(atypeFactory);
    }
}
