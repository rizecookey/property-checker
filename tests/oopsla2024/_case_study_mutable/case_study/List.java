package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class List {

    public @MaybeAliased Object head;

    public
    @Unique
    @Nullable @Length(min="this.size - 1", max="this.size - 1")
    List tail;

    public @Positive int size;

    @JMLClause("ensures this.tail == tail && this.head == head;")
    @JMLClause("assignable \\nothing;")
    public
    @Unique @Length(min="tail.size + 1", max="tail.size + 1")
    // :: error: nullness.inconsistent.constructor.type :: error: length.inconsistent.constructor.type
    List(
            Object head,
            List tail) {
        this.size = tail.size() + 1;
        this.head = head;
        this.tail = tail;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == head;")
    @JMLClause("assignable \\nothing;")
    public
    @Unique @Length(min="1", max="1")
    // :: error: nullness.inconsistent.constructor.type :: error: length.inconsistent.constructor.type
    List(Object head) {
        this.size = 1;
        this.head = head;
        this.tail = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == newHead;")
    @JMLClause("assignable this.*;")
    public void insertFront(
            @Unique List this,
            Object newHead) {
        Packing.unpack(this, List.class);
        if (tail == null) {
            this.tail = new List(this.head);
        } else {
            // :: error: argument.type.incompatible
            this.tail = new List(this.head, this.tail);
        }
        this.head = newHead;
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == newHead;")
    @JMLClause("assignable this.*;")
    @EnsuresReadOnly(value="#1")
    public void appendBack(
            @Unique List this,
            @Unique List other) {
        Packing.unpack(this, List.class);
        if (tail == null) {
            this.tail = other;
            this.size += List.size(other);
        } else {
            this.tail.appendBack(other);
        }
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures \\result == this.head;")
    @JMLClause("assignable \\nothing;")
    public @ReadOnly Object getHead(@ReadOnly List this) {
        return this.head;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\nothing;")
    @Nullable
    @Length(min="this.size - 1", max="this.size - 1")
    public @ReadOnly List getTail(@ReadOnly List this) {
        return this.tail;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\nothing")
    @EnsuresReadOnly("this")
    @Nullable
    @Length(min="this.size - 1", max="this.size - 1")
    public @Unique List stealTail(@Unique List this) {
        Packing.unpack(this, List.class);
        // :: error: return.type.incompatible
        return this.tail;
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\nothing;")
    public @Positive int size(@ReadOnly List this) {
        return this.size;
    }

    @JMLClause("ensures l != null ==> \\result == l.size;")
    @JMLClause("ensures l == null ==> \\result == 0;")
    @JMLClause("assignable \\nothing;")
    public static @NonNegative int size(@ReadOnly List l) {
        if (l == null) {
            return 0;
        } else {
            // :: error: method.invocation.invalid
            return l.size();
        }
    }
}
