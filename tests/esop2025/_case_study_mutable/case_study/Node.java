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
@JMLClause("public ghost \\seq nodeseq;")
@JMLClause("public accessible \\inv: footprint;")
// packed field not included in footprint
@JMLClause("public invariant this.footprint == (\\infinite_union; int i; 0 <= i < nodeseq.length; \\set_union(\\singleton(((Node)nodeseq)[i].head), \\singleton(((Node)nodeseq)[i].tail), \\singleton(((Node)nodeseq)[i].footprint));")
@JMLClause("public invariant this.tail != null ==> this.tail.nodeseq == this.nodeseq[1..this.nodeseq.length] && \\disjoint(this.*, this.tail.footprint);")
@JMLClause("public invariant (\\forall int i; 0 <= i < nodeseq.length; ((Node)nodeseq)[i] != null);")
@JMLClause("public invariant this.tail == null || \\invariant_for(this.tail);")
public final class Node {

    public @MaybeAliased Order head;
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
        Ghost.set("nodeseq", "\\seq_concat(\\seq_singleton(this.tail), this.tail.nodeseq)");
        Ghost.set("footprint", "(\\infinite_union; int i; 0 <= i < nodeseq.length; \\set_union(\\singleton(((Node)nodeseq)[i].head), \\singleton(((Node)nodeseq)[i].tail), \\singleton(((Node)nodeseq)[i].footprint)))");
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
        Ghost.set("nodeseq", "\\seq_empty");
        Ghost.set("footprint", "(\\infinite_union; int i; 0 <= i < nodeseq.length; \\set_union(\\singleton(((Node)nodeseq)[i].head), \\singleton(((Node)nodeseq)[i].tail), \\singleton(((Node)nodeseq)[i].footprint)))");
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
        Ghost.set("nodeseq", "\\seq_concat(\\seq_singleton(this.tail), this.tail.nodeseq)");
        Ghost.set("footprint", "(\\infinite_union; int i; 0 <= i < nodeseq.length; \\set_union(\\singleton(((Node)nodeseq)[i].head), \\singleton(((Node)nodeseq)[i].tail), \\singleton(((Node)nodeseq)[i].footprint)))");
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
        if (this.tail == null) {
            this.tail = new Node(newHead);
        } else {
            // :: error: nullness.method.invocation.invalid
            this.tail.insert(newHead);
        }
        Packing.pack(this, Node.class);
        Ghost.set("nodeseq", "\\seq_concat(\\seq_singleton(this.tail), this.tail.nodeseq)");
        Ghost.set("footprint", "(\\infinite_union; int i; 0 <= i < nodeseq.length; \\set_union(\\singleton(((Node)nodeseq)[i].head), \\singleton(((Node)nodeseq)[i].tail), \\singleton(((Node)nodeseq)[i].footprint)))");
    }

    @JMLClause("ensures \\result == this.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Order getHead(@Unique Node this) {
        return this.head;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @ReadOnly @Nullable Node getTail(@Unique Node this) {
        return this.tail;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable this.packed;")
    @EnsuresReadOnly("this")
    @EnsuresUnknownInit(value="this", targetValue=Object.class)
    public
    @Unique @Nullable @Sorted Node
    stealTail(@Unique Node this) {
        Packing.unpack(this, Node.class);
        return this.tail;
    }
}
