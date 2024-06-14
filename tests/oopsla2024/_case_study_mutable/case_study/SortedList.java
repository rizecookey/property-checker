package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class SortedList {

    public @Unique @Nullable @Sorted SortedListNode first;

    public @NonNegative int size;

    @JMLClause("ensures this.first == null && this.size == 0;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: empty.inconsistent.constructor.type
    public @PossiblyEmpty SortedList() {
        this.size = 0;
        this.first = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, SortedList.class);
    }

    @EnsuresNonEmpty(value="this")
    @JMLClause("assignable this.*, \\infinite_union(SortedListNode n; n.*);")
    // :: error: empty.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @PossiblyEmpty SortedList this,
            int newHead) {
        Packing.unpack(this, SortedList.class);
        if (first == null) {
            this.first = new SortedListNode(newHead);
        } else {
            // :: error: nullness.method.invocation.invalid
            this.first.insert(newHead);
        }
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, SortedList.class);
    }

    @JMLClause("ensures \\old(this.first).head == \\result;")
    @JMLClause("assignable this.*, this.first.packed;")
    @EnsuresPossiblyEmpty(value="this")
    // :: error: empty.contracts.postcondition.not.satisfied
    public int remove(@Unique @NonEmpty SortedList this) {
        // :: error: nullness.method.invocation.invalid
        int result = this.first.getHead();
        Packing.unpack(this, SortedList.class);
        this.first = this.first.stealTail();
        --this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, SortedList.class);
        return result;
    }

    @JMLClause("ensures \\old(this.first) != null ==> \\result == \\old(this.first).head;")
    @JMLClause("ensures \\old(this.first) == null ==> \\result == -1;")
    @JMLClause("assignable this.*, this.first.packed;")
    public @Nullable int removeIfPresent(@Unique @PossiblyEmpty SortedList this) {
        if (this.first != null) {
            // :: error: empty.method.invocation.invalid
            return this.remove();
        } else {
            return -1;
        }
    }

    @JMLClause("ensures \\result == this.first.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased int getHead(@Unique @NonEmpty SortedList this) {
        // :: error: nullness.method.invocation.invalid
        return this.first.getHead();
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique @PossiblyEmpty SortedList this) {
        return this.size;
    }
}
