package edu.kit.kastel.property.packing;

import org.checkerframework.checker.initialization.InitializationAbstractTransfer;
import org.checkerframework.framework.flow.CFValue;

public class PackingTransfer extends InitializationAbstractTransfer<CFValue, PackingStore, PackingTransfer> {

    public PackingTransfer(PackingAnalysis analysis) {
        super(analysis);
    }
}
