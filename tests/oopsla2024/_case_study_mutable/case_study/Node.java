package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Node {

    public @MaybeAliased Object head;

    public
    @Unique
    @Nullable @Length(min="this.size - 1", max="this.size - 1")
    Node tail;

    public @Positive int size;

    @JMLClause("ensures this.tail == tail && this.head == head && this.size == tail.size + 1;")
    @JMLClause("assignable \\nothing;")
    @EnsuresReadOnly(value="#2")
    public
    @Unique @Length(min="tail.size + 1", max="tail.size + 1")
    // :: error: length.inconsistent.constructor.type
    Node(Object head,  @Unique Node tail) {
        this.size = tail.size() + 1;
        this.head = head;
        this.tail = tail;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Node.class);
    }

    @JMLClause("ensures this.head == head && this.tail == null && this.size == 1;")
    @JMLClause("assignable \\nothing;")
    public
    @Unique @Length(min="1", max="1")
    // :: error: length.inconsistent.constructor.type
    Node(Object head) {
        this.size = 1;
        this.head = head;
        this.tail = null;
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
    public @MaybeAliased Object getHead(@Unique Node this) {
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
    @Unique @Nullable @Length(min="this.size - 1", max="this.size - 1") Node
    stealTail(@Unique Node this) {
        Packing.unpack(this, Node.class);
        // :: error: length.return.type.incompatible
        return this.tail;
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @Positive int size(@Unique Node this) {
        return this.size;
    }
}
