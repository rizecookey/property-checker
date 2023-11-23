package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.common.basetype.BaseTypeChecker;

/**
 * This is the entry point for exclusivity type-checking.
 */
public class ExclusivityChecker extends BaseTypeChecker {
    
    @Override
    public ExclusivityAnnotatedTypeFactory getTypeFactory() {
        return (ExclusivityAnnotatedTypeFactory) super.getTypeFactory();
    }
}
