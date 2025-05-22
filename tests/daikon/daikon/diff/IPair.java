package daikon.diff;

import java.util.Objects;
import org.plumelib.util.*;
import org.checkerframework.checker.lock.qual.GuardSatisfied;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;
import org.checkerframework.dataflow.qual.SideEffectFree;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.Dependable;

// Simplified version of plumelib class for Kukicha case study
public class IPair<@MaybeAliased V1, @MaybeAliased V2> {

    /** The first element of the pair. */
    public final @Dependable V1 first;

    /** The second element of the pair. */
    public final @Dependable V2 second;

    private IPair(V1 first, V2 second) {
        this.first = first;
        this.second = second;
    }

    public static <T1, T2> IPair<T1, T2> of(T1 first, T2 second) {
        return new IPair<>(first, second);
    }
}
