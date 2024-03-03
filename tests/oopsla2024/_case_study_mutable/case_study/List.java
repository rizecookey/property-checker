package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class List {

    public @MaybeAliased Object head;

    public
    @Unique
    @Nullable @Length(min="this.size - 1", max="this.size - 1")
    List tail;

    public @Positive int size;

    @JMLClause("ensures this.tail == tail && this.head == head && this.size == tail.size + 1;")
    @JMLClause("assignable \\nothing;")
    @EnsuresReadOnly(value="#2")
    public
    @Unique @Length(min="tail.size + 1", max="tail.size + 1")
    // :: error: length.inconsistent.constructor.type
    List(Object head,  @Unique List tail) {
        this.size = tail.size() + 1;
        this.head = head;
        this.tail = tail;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == head && this.tail == null && this.size == 1;")
    @JMLClause("assignable \\nothing;")
    public
    @Unique @Length(min="1", max="1")
    // :: error: length.inconsistent.constructor.type
    List(Object head) {
        this.size = 1;
        this.head = head;
        this.tail = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == newHead;")
    @JMLClause("assignable this.*;")
    @EnsuresLength(value="this", min="n+1", max="m+1")
    // :: error: length.contracts.postcondition.not.satisfied
    public void insertFront(
            @Unique @Length(min="n", max="m") List this,
            Object newHead,
            @NonNegative int n, @NonNegative int m) {
        Packing.unpack(this, List.class);
        if (tail == null) {
            this.tail = new List(this.head);
        } else {
            // :: error: nullness.argument.type.incompatible
            this.tail = new List(this.head, this.tail);
        }
        this.head = newHead;
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @EnsuresReadOnly(value="#1")
    @EnsuresLength(value="this", min="n+l", max="m+k")
    // :: error: length.contracts.postcondition.not.satisfied
    public void appendBack(
            @Unique @Length(min="n", max="m") List this,
            @Unique @Length(min="l", max="k") List other,
            @NonNegative int n, @NonNegative int m,
            @NonNegative int l, @NonNegative int k) {
        Packing.unpack(this, List.class);
        this.size += other.size();
        if (tail == null) {
            this.tail = other;
        } else {
            // :: error: length.method.invocation.invalid :: error: nullness.method.invocation.invalid :: error: length.argument.type.incompatible
            this.tail.appendBack(other, clampTo0(n), clampTo0(m), l, k);
        }
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
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
    public @MaybeAliased Object getHead(@Unique List this) {
        return this.head;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @ReadOnly @Nullable List getTail(@Unique List this) {
        return this.tail;
    }

    @JMLClause("ensures \\result == this.tail;")
    @JMLClause("assignable this.packed;")
    @EnsuresReadOnly("this")
    @EnsuresUnknownInit(value="this", targetValue=Object.class)
    public
    @Unique @Nullable @Length(min="this.size - 1", max="this.size - 1") List
    stealTail(@Unique List this) {
        Packing.unpack(this, List.class);
        // :: error: length.return.type.incompatible
        return this.tail;
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @Positive int size(@Unique List this) {
        return this.size;
    }

    @JMLClause("ensures l != null ==> \\result == l.size;")
    @JMLClause("ensures l == null ==> \\result == 0;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public static @NonNegative int size(@Unique @Nullable List l) {
        if (l == null) {
            return 0;
        } else {
            // :: error: nullness.method.invocation.invalid
            return l.size();
        }
    }
}
