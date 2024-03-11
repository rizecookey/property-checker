package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

/*@JMLClause("public model instance \\locset footprint;")
@JMLClause("public represents footprint = this.head, this.tail, this.size, tail == null ? \\empty : tail.footprint;")
@JMLClause("public accessible footprint : footprint;")*/
public final class Node {

    public @MaybeAliased Order head;

    public @Unique @Nullable @Sorted Node tail;

    public @Positive int size;

    @JMLClause("requires head.product.price <= tail.head.product.price;")
    @JMLClause("ensures this.tail == tail && this.head == head && this.size == tail.size + 1;")
    @JMLClause("assignable \\nothing;") @Pure
    @EnsuresReadOnly(value="#2")
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    Node(Order head,  @Unique @Sorted Node tail) {
        this.size = tail.size() + 1;
        this.head = head;
        this.tail = tail;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("ensures this.head == head && this.tail == null && this.size == 1;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    @Unique @Sorted
    // :: error: sorted.inconsistent.constructor.type
    Node(Order head) {
        this.size = 1;
        this.head = head;
        this.tail = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(Node n; n.*);")
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
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable this.*;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertHead(
            @Unique @Sorted Node this,
            Order newHead) {
        Packing.unpack(this, Node.class);
        int size = this.size;
        if (this.tail == null) {
            this.tail = new Node(this.head);
        } else {
            // :: error: nullness.argument.type.incompatible
            this.tail = new Node(this.head, this.tail);
        }
        this.head = newHead;
        ++this.size;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("requires newHead.product.price >= this.head.product.price;")
    @JMLClause("ensures this.head == \\old(this.head);")
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(Node n; n.*);")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertTail(
            @Unique @Sorted Node this,
            Order newHead) {
        if (this.tail == null) {
            Packing.unpack(this, Node.class);
            this.tail = new Node(newHead);
            ++this.size;
            // :: error: initialization.fields.uninitialized
            Packing.pack(this, Node.class);
        } else {
            // :: error: nullness.method.invocation.invalid
            if (newHead.getPrice() <= this.tail.getHead().getPrice()) {
                this.insertTailHead(newHead);
            } else {
                this.insertTailTail(newHead);
            }
        }
    }

    @JMLClause("requires this.tail != null && newHead.product.price <= this.tail.head.product.price;")
    @JMLClause("requires newHead.product.price >= this.head.product.price;")
    @JMLClause("ensures this.head == \\old(this.head);")
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable this.*, this.tail.*;")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertTailHead(
            @Unique @Sorted Node this,
            Order newHead) {
        Packing.unpack(this, Node.class);

        // :: error: nullness.method.invocation.invalid
        this.tail.insertHead(newHead);
        ++size;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("requires this.tail != null && newHead.product.price >= this.tail.head.product.price;")
    @JMLClause("requires newHead.product.price >= this.head.product.price;")
    @JMLClause("ensures this.head == \\old(this.head);")
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(Node n; n.*);")
    // :: error: sorted.contracts.postcondition.not.satisfied
    private void insertTailTail(
            @Unique @Sorted Node this,
            Order newHead) {
        Packing.unpack(this, Node.class);

        Order head = this.head;
        @Unique Node tail = this.tail;
        int size = this.size;

        // :: error: nullness.method.invocation.invalid
        tail.insertTail(newHead);

        this.head = head;
        this.tail = tail;
        this.size = size + 1;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("ensures i >= 0 ==> \\result == i;")
    @JMLClause("ensures i <= 0 ==> \\result == 0;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    private static @NonNegative int clampTo0(int i) {
        // :: error: sign.return.type.incompatible
        return i >= 0 ? i : 0;
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

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @Positive int size(@Unique Node this) {
        return this.size;
    }
}
