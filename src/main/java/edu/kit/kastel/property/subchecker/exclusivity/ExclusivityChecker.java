package edu.kit.kastel.property.subchecker.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.util.Set;

/**
 * This is the entry point for exclusivity type-checking.
 */
public class ExclusivityChecker extends BaseTypeChecker {

    public ExclusivityChecker(PropertyChecker parent) {
        setProcessingEnvironment(parent.getProcessingEnvironment());
        treePathCacher = parent.getTreePathCacher();
        setParentChecker(parent);
    }

    public ExclusivityChecker() { }

    @Override
    protected Set<Class<? extends BaseTypeChecker>> getImmediateSubcheckerClasses() {
        Set<Class<? extends BaseTypeChecker>> checkers = super.getImmediateSubcheckerClasses();
        checkers.add(PackingFieldAccessSubchecker.class);
        return checkers;
    }

    @Override
    public ExclusivityAnnotatedTypeFactory getTypeFactory() {
        return (ExclusivityAnnotatedTypeFactory) super.getTypeFactory();
    }
}
