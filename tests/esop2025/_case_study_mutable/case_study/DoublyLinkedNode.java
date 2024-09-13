package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

// TODO: Supress all warnings here and use KeY only. Cmp. KaJaVe
// Manually ensure that this code never calls impure type-checked code
// and never creates aliases of typed-checked variables.
// Then state conformance is preserved by treating everything in here as maybe-aliased and unpacked.

@JMLClause("public model \\locset footprint;")
@JMLClause("public accessible footprint: footprint;")
// packed field not included in footprint
@JMLClause("public represents this.footprint = \\set_union(\\singleton(this.datum), \\singleton(this.prev), \\singleton(this.next), this.next == null ? \\empty : this.next.footprint, this.prev == null ? \\empty : this.prev.footprint);")
@JMLClause("public invariant this.next != null ==> \\disjoint(this.*, this.next.footprint);")
@JMLClause("public invariant this.prev != null ==> \\disjoint(this.*, this.prev.footprint);")
@JMLClause("public invariant this.next != null && this.prev != null ==> \\disjoint(this.next.footprint, this.prev.footprint);")
@JMLClause("public invariant next == null || this.datum.product.price <= next.datum.product.price;")
@JMLClause("public invariant this.prev == null || \\invariant_for(this.prev);")
@JMLClause("public invariant this.next == null || \\invariant_for(this.next);")
public final class DoublyLinkedNode {

    public Order datum;

    public DoublyLinkedNode prev;
    public DoublyLinkedNode next;

    @JMLClause("requires \\invariant_for(prev) && \\invariant_for(next);")
    @JMLClause("requires datum.product.price <= next.datum.product.price;")
    @JMLClause("requires prev.datum.product.price <= datum.product.price;")
    @JMLClause("ensures this.datum == datum && this.next == next && this.prev == prev;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    DoublyLinkedNode(Order datum,
                     @Nullable DoublyLinkedNode next,
                     @Nullable DoublyLinkedNode prev) {
        this.datum = datum;
        this.prev = prev;
        this.next = next;
    }

    @JMLClause("ensures this.datum == datum && this.prev == null && this.next == null;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    @MaybeAliased
    DoublyLinkedNode(Order datum) {
        this.datum = datum;
        this.prev = null;
        this.next = null;
    }

    @JMLClause("requires newDatum.product.price <= this.datum.product.price;")
    @JMLClause("ensures this.prev != null && this.prev.datum == newDatum;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    protected DoublyLinkedNode insertPrev(
            DoublyLinkedNode this,
            Order newDatum) {
        if (this.prev == null) {
            this.prev = new DoublyLinkedNode(newDatum, this, null);
        } else {
            DoublyLinkedNode newPrev = new DoublyLinkedNode(newDatum, this, this.prev);
            this.prev.setNext(newPrev);
            this.prev = newPrev;
        }

        return this.prev;
    }

    @JMLClause("requires newDatum.product.price >= this.datum.product.price;")
    @JMLClause("ensures this.next != null && this.next.datum.product.price >= newDatum.product.price;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    protected DoublyLinkedNode insertNext(
            DoublyLinkedNode this,
            Order newDatum) {
        if (this.next == null) {
            this.next = new DoublyLinkedNode(newDatum, null, this);
            return this.next;
        } else if (this.next.getPrice() <= newDatum.getPrice()) {
            return this.next.insertPrev(newDatum);
        } else {
            return this.next.insertNext(newDatum);
        }
    }

    @JMLClause("ensures \\result == this.datum;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public Order getDatum(DoublyLinkedNode this) {
        return this.datum;
    }

    @JMLClause("ensures \\result == this.datum.product.price;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getPrice(DoublyLinkedNode this) {
        return this.datum.getPrice();
    }

    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    public DoublyLinkedNode remove(DoublyLinkedNode this) {
        DoublyLinkedNode oldPrev = this.prev;
        DoublyLinkedNode oldNext = this.next;

        oldPrev.setNext(oldNext);
        oldNext.setPrev(oldPrev);

        this.next = null;
        this.prev = null;

        return oldNext;
    }

    @JMLClause("ensures this.next == newNode;")
    @JMLClause("assignable this.next;")
    protected void setNext(DoublyLinkedNode this, DoublyLinkedNode newNode) {
        this.next = newNode;
    }

    @JMLClause("ensures this.prev == newNode;")
    @JMLClause("assignable this.prev;")
    protected void setPrev(DoublyLinkedNode this, DoublyLinkedNode newNode) {
        this.prev = newNode;
    }
}
