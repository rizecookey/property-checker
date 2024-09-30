package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.util.Ghost;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClause("public ghost \\locset footprint;")
@JMLClause("public accessible \\inv: footprint;")
// packed field not included in footprint
@JMLClause("public invariant this.footprint == \\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first == null ? \\empty : this.first.footprint);")
@JMLClause("public invariant this.first == null || \\invariant_for(this.first);")
@JMLClause("public invariant this.first != null ==> \\disjoint(this.*, this.first.footprint);")
public final class SortedList {

    public @Unique @Nullable @Sorted Node first;

    @JMLClause("ensures this.first == null;")
    @JMLClause("ensures \\fresh(this.footprint);")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: empty.inconsistent.constructor.type
    public @PossiblyEmpty SortedList() {
        this.first = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, SortedList.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint))");
    }

    @EnsuresNonEmpty(value="this")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: empty.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @PossiblyEmpty SortedList this,
            Order newHead) {
        Packing.unpack(this, SortedList.class);
        @Unique Node first = this.first;
        if (first == null) {
            first = new Node(newHead);
        } else {
            // :: error: nullness.method.invocation.invalid
            first.insert(newHead);
        }
        this.first = first;
        Packing.pack(this, SortedList.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first.footprint)");
    }

    @JMLClause("ensures \\old(this.first).head == \\result;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint, this.first.packed;")
    @EnsuresPossiblyEmpty(value="this")
    // :: error: empty.contracts.postcondition.not.satisfied
    public Order remove(@Unique @NonEmpty SortedList this) {
        // :: error: nullness.method.invocation.invalid
        Order result = this.first.getHead();
        Packing.unpack(this, SortedList.class);
        this.first = this.first.stealTail();
        Packing.pack(this, SortedList.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.first), \\singleton(this.footprint), this.first == null ? \\empty : this.first.footprint)");
        return result;
    }

    @JMLClause("ensures \\old(this.first) != null ==> \\result == \\old(this.first).head;")
    @JMLClause("ensures \\old(this.first) == null ==> \\result == null;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint, this.first.packed;")
    public @Nullable Order removeIfPresent(@Unique @PossiblyEmpty SortedList this) {
        if (this.first != null) {
            // :: error: empty.method.invocation.invalid
            return this.remove();
        } else {
            return null;
        }
    }

    @JMLClause("ensures \\result == this.first.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Order getHead(@Unique @NonEmpty SortedList this) {
        // :: error: nullness.method.invocation.invalid
        return this.first.getHead();
    }
}
