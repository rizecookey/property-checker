package edu.kit.kastel.property.subchecker.nullness;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.checkerframework.checker.nullness.KeyForSubchecker;

import javax.annotation.processing.SupportedOptions;

@SupportedOptions({"assumeKeyFor"})
public class KeyForLatticeSubchecker extends KeyForSubchecker {

    private PropertyChecker parent;

    public KeyForLatticeSubchecker(PropertyChecker parent) {
        this.parent = parent;

        setProcessingEnvironment(parent.getProcessingEnvironment());
        treePathCacher = parent.getTreePathCacher();
        setParentChecker(parent);
    }

    public PropertyChecker getParent() {
        return parent;
    }
}
