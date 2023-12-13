package edu.kit.kastel.property.subchecker.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.File;

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
    public ExclusivityAnnotatedTypeFactory getTypeFactory() {
        return (ExclusivityAnnotatedTypeFactory) super.getTypeFactory();
    }
}
