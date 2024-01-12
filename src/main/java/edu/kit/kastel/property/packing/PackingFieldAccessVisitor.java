package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationFieldAccessVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class PackingFieldAccessVisitor extends InitializationFieldAccessVisitor {

    public PackingFieldAccessVisitor(BaseTypeChecker checker) {
        super(checker);
    }
}
