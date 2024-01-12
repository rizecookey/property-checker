package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAnnotatedTypeFactory;
import org.checkerframework.checker.initialization.InitializationChecker;
import org.checkerframework.checker.initialization.InitializationVisitor;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.util.NavigableSet;
import java.util.Set;

public abstract class PackingChecker extends InitializationChecker {

    @Override
    public NavigableSet<String> getSuppressWarningsPrefixes() {
        NavigableSet<String> result = super.getSuppressWarningsPrefixes();
        // The default prefix "packing" must be added manually because this checker class
        // is abstract and its subclasses are not named "PackingChecker".
        result.add("packing");
        return result;
    }

    @Override
    public PackingAnnotatedTypeFactory getTypeFactory() {
        return (PackingAnnotatedTypeFactory) super.getTypeFactory();
    }

    @Override
    protected PackingVisitor createSourceVisitor() {
        return new PackingVisitor(this);
    }
}
