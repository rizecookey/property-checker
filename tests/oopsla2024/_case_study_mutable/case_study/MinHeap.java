package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class MinHeap {

    public @Unique @Nullable @HeapProperty MinHeapNode root;

    public @NonNegative int size;

    @JMLClause("ensures this.root == null && this.size == 0;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: empty.inconsistent.constructor.type
    public @PossiblyEmptyMinHeap MinHeap() {
        this.size = 0;
        this.root = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeap.class);
    }

    @EnsuresNonEmptyMinHeap(value="this")
    @JMLClause("assignable this.*, \\infinite_union(MinHeapNode n; n.*);")
    // :: error: empty.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @PossiblyEmptyMinHeap MinHeap this,
            int newDatum) {
        Packing.unpack(this, MinHeap.class);
        if (this.root == null) {
            this.root = new MinHeapNode(newDatum);
        } else {
            // :: error: nullness.method.invocation.invalid
            this.root.insert(newDatum);
        }
        Packing.pack(this, MinHeap.class);
    }

    @JMLClause("assignable this.*, \\infinite_union(MinHeapNode n; n.*);")
    public int insertThenRemove(
            @Unique @PossiblyEmptyMinHeap MinHeap this,
            int newDatum) {
        if (this.root == null) {
            return newDatum;
        } else {
            Packing.unpack(this, MinHeap.class);
            // :: error: nullness.method.invocation.invalid
            int result = this.root.insertThenRemove(newDatum);
            Packing.pack(this, MinHeap.class);
            return result;
        }
    }

    @JMLClause("ensures \\result == this.root.datum;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased int getRoot(@Unique @NonEmptyMinHeap MinHeap this) {
        return this.root.getDatum();
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique @PossiblyEmptyMinHeap MinHeap this) {
        return this.size;
    }
}
