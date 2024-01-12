package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class PackingVisitor extends InitializationVisitor {

    public PackingVisitor(BaseTypeChecker checker) {
        super(checker);
    }
}
