package edu.kit.kastel.property.subchecker.nullness;

import org.checkerframework.checker.nullness.NullnessNoInitAnalysis;
import org.checkerframework.checker.nullness.NullnessNoInitAnnotatedTypeFactory;
import org.checkerframework.checker.nullness.NullnessNoInitStore;
import org.checkerframework.common.basetype.BaseTypeChecker;

public class NullnessLatticeAnalysis extends NullnessNoInitAnalysis {
    /**
     * Creates a new {@code NullnessAnalysis}.
     *
     * @param checker the checker
     * @param factory the factory
     */
    public NullnessLatticeAnalysis(BaseTypeChecker checker, NullnessNoInitAnnotatedTypeFactory factory) {
        super(checker, factory);
    }

    @Override
    public NullnessNoInitStore createEmptyStore(boolean sequentialSemantics) {
        return new NullnessLatticeStore(this, sequentialSemantics);
    }

    @Override
    public NullnessNoInitStore createCopiedStore(NullnessNoInitStore s) {
        return new NullnessLatticeStore(s);
    }
}
