package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractStore;
import org.checkerframework.framework.flow.CFValue;

public class PackingStore extends InitializationAbstractStore<CFValue, PackingStore> {

    public PackingStore(PackingAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    public PackingStore(PackingStore other) {
        super(other);
    }
}
