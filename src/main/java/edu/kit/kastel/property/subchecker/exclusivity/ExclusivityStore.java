package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.framework.flow.CFAbstractStore;

public class ExclusivityStore extends CFAbstractStore<ExclusivityValue, ExclusivityStore> {

    protected ExclusivityStore(ExclusivityAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
    }

    protected ExclusivityStore(ExclusivityStore other) {
        super(other);
    }
}
