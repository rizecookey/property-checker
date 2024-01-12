package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationStore;

public class PackingStore extends InitializationStore {

    public PackingStore(PackingAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    public PackingStore(PackingStore other) {
        super(other);
    }
}
