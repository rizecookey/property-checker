package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClause("public ghost \\locset footprint;")
@JMLClause("public accessible \\inv: footprint;")
// packed field not included in footprint
@JMLClause("public invariant this.footprint == \\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail == null ? \\empty : this.tail.footprint);")
@JMLClause("public invariant this.tail != null ==> \\disjoint(this.*, this.tail.footprint);")
@JMLClause("public invariant this.tail == null || \\invariant_for(this.tail);")
public final class Node {

    public @MaybeAliased Order head;

    // See the comment about SortedList::first in SortedList class.
    public @Unique @Nullable @Sorted Node tail;

    @JMLClause("requires \\invariant_for(tail);")
    @JMLClause("requires head.product.price <= tail.head.product.price;")
    @JMLClause("ensures this.tail == tail && this.head == head;")
    @JMLClause("assignable \\nothing;") @Pure
    @EnsuresReadOnly(value="#2")
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    Node(Order head, @Unique @Sorted Node tail) {
        this.head = head;
        this.tail = tail;
        Packing.pack(this, Node.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");
    }

    @JMLClause("ensures this.head == head && this.tail == null;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    Node(Order head) {
        this.head = head;
        this.tail = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint))");
    }

    @JMLClause("ensures this.head == \\old(this.head) || this.head == newHead;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    public void insert(
            @Unique @Sorted Node this,
            Order newHead) {
        if (newHead.getPrice() <= this.head.getPrice()) {
            this.insertHead(newHead);
        } else {
            this.insertTail(newHead);
        }
    }
    
    @JMLClause("requires newHead.product.price <= this.head.product.price;")
    @JMLClause("ensures this.head == newHead;")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertHead(
            @Unique @Sorted Node this,
            Order newHead) {
        Packing.unpack(this, Node.class);
        if (this.tail == null) {
            this.tail = new Node(this.head);
        } else {
            // :: error: nullness.argument.type.incompatible
            this.tail = new Node(this.head, this.tail);
        }
        this.head = newHead;

        Packing.pack(this, Node.class);
        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");
    }

    @JMLClause("requires this.head.product.price <= newHead.product.price;")
    @JMLClause("ensures this.head == \\old(this.head);")
    @JMLClause("ensures \\new_elems_fresh(this.footprint);")
    @JMLClause("assignable this.footprint;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertTail(
            @Unique @Sorted Node this,
            Order newHead) {
        Packing.unpack(this, Node.class);

        if (tail == null) {
            this.tail = new Node(newHead);
        } else {
            // :: error: nullness.method.invocation.invalid
            this.tail.insert(newHead);
        }

        Packing.pack(this, Node.class);

        Ghost.set("footprint", "\\set_union(\\singleton(this.head), \\singleton(this.tail), \\singleton(this.footprint), this.tail.footprint)");

        // These statements use the uniqueness and packing type systems to tell KeY that certain heap locations are immutable.
        // E.g., the first statement translates to `//@ assume this.head == \old(this.head) ==> this.head.product.price == \old(this.head.product.price)`,
        // which is sound because `this.head` is `@MaybeAliased @Packed(Order.class)` and thus immutable.
        Assert.immutableFieldUnchanged("this.head", "this.head.product.price");
        Assert.immutableFieldUnchanged("this.tail.head", "this.tail.head.product.price");
        Assert.immutableFieldEqual("this.tail.head", "newHead", "this.tail.head.product.price", "newHead.product.price");
    }

    @JMLClause("ensures \\result == this.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Order getHead(@Unique @Sorted Node this) {
        return this.head;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @ReadOnly @Nullable Node getTail(@Unique @Sorted Node this) {
        return this.tail;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("ensures \\result != null ==> \\invariant_for(\\result);")
    @JMLClause("assignable this.packed;")
    @EnsuresReadOnly("this")
    @EnsuresUnknownInit(value="this", targetValue=Object.class)
    public
    @Unique @Nullable @Sorted Node
    stealTail(@Unique @Sorted Node this) {
        Packing.unpack(this, Node.class);
        return this.tail;
    }
}
