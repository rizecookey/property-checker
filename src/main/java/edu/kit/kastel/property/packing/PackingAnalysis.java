package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAnalysis;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class PackingAnalysis extends InitializationAnalysis {

    protected PackingAnalysis(BaseTypeChecker checker, PackingAnnotatedTypeFactory factory) {
        super(checker, factory);
    }
}
