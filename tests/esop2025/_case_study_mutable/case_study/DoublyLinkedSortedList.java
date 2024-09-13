package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

// in every list client: public invariant \invariant_for(this.list);
@JMLClause("public invariant \\invariant_for(this.first) && \\invariant_for(this.last);")
@JMLClause("public model \\locset footprint;")
@JMLClause("public accessible footprint: footprint;")
// packed field not included in footprint
@JMLClause("public represents this.footprint = \\set_union(\\singleton(this.first), \\singleton(this.last), \\singleton(this.size), this.first == null ? \\empty : this.first.footprint, this.last == null ? \\empty : this.last.footprint);")
@JMLClause("public invariant this.first != null ==> \\disjoint(this.*, this.first.footprint);")
@JMLClause("public invariant this.last != null ==> \\disjoint(this.*, this.last.footprint);")
public final class DoublyLinkedSortedList {

    public @Nullable @MaybeAliased DoublyLinkedNode first;
    public @Nullable @MaybeAliased DoublyLinkedNode last;

    public @NonNegative int size;

    @JMLClause("ensures this.first == null && this.last == null && this.size == 0;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: emptydl.inconsistent.constructor.type
    public @PossiblyEmptyDoublyLinked DoublyLinkedSortedList() {
        this.size = 0;
        this.first = null;
        this.last = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, DoublyLinkedSortedList.class);
    }

    @EnsuresNonEmptyDoublyLinked(value="this")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: emptydl.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @PossiblyEmptyDoublyLinked DoublyLinkedSortedList this,
            Order newDatum) {
        Packing.unpack(this, DoublyLinkedSortedList.class);
        if (this.first == null) {
            this.first = new DoublyLinkedNode(newDatum);
            this.last = this.first;
        // :: error: nullness.method.invocation.invalid
        } else if (this.first.getPrice() >= newDatum.getPrice()) {
            this.first = this.first.insertPrev(newDatum);
        // :: error: nullness.method.invocation.invalid
        } else if (this.last.getPrice() <= newDatum.getPrice()) {
            this.last = this.last.insertNext(newDatum);
        } else {
            this.first.insertNext(newDatum);
        }
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, DoublyLinkedSortedList.class);
    }

    @JMLClause("ensures \\old(this.first).datum == \\result;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    @EnsuresPossiblyEmptyDoublyLinked(value="this")
    // :: error: emptydl.contracts.postcondition.not.satisfied
    public Order remove(@Unique @NonEmptyDoublyLinked DoublyLinkedSortedList this) {
        // :: error: nullness.method.invocation.invalid
        Order result = this.first.getDatum();
        Packing.unpack(this, DoublyLinkedSortedList.class);
        this.first = this.first.remove();
        if (this.first == null) {
            this.last = null;
        }
        --this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, DoublyLinkedSortedList.class);
        return result;
    }

    @JMLClause("ensures \\old(this.first) != null ==> \\result == \\old(this.first).datum;")
    @JMLClause("ensures \\old(this.first) == null ==> \\result == null;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    public @Nullable Order removeIfPresent(@Unique @PossiblyEmptyDoublyLinked DoublyLinkedSortedList this) {
        if (this.first != null) {
            // :: error: emptydl.method.invocation.invalid
            return this.remove();
        } else {
            return null;
        }
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique @PossiblyEmptyDoublyLinked DoublyLinkedSortedList this) {
        return this.size;
    }
}
