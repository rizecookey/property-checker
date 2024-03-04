package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class List {

    public
    @Unique
    @Nullable @Length(min="this.size", max="this.size")
    List first;

    public @NonNegative int size;

    @JMLClause("ensures this.first == null && this.size == 0;")
    @JMLClause("assignable \\nothing;")
    public
    @Unique @Length(min="0", max="0")
    // :: error: length.inconsistent.constructor.type
    List() {
        this.size = 0;
        this.first = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.first.head == newHead;")
    @JMLClause("assignable this.*;")
    @EnsuresLength(value="this", min="n+1", max="m+1")
    // :: error: length.contracts.postcondition.not.satisfied
    public void insertFront(
            @Unique @Length(min="n", max="m") List this,
            Object newHead,
            @NonNegative int n, @NonNegative int m) {
        Packing.unpack(this, List.class);
        if (first == null) {
            this.first = new Node(newHead);
        } else {
            // :: error: nullness.argument.type.incompatible
            this.first = new List(newHead, this.first);
        }
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures \\old(this.first).head == \\result;")
    @JMLClause("assignable this.*;")
    @EnsuresLength(value="this", min="n-1", max="m-1")
    // :: error: length.contracts.postcondition.not.satisfied
    public Object removeFront(
            @Unique @Length(min="n", max="m") List this,
            Object newHead,
            @Positive int n, @Positive int m) {
        Object result = this.first.getHead();
        Packing.unpack(this, List.class);
        this.first = this.first.stealTail();
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
        return result;
    }

    @JMLClause("ensures \\result == this.first.head;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @MaybeAliased Object getHead(
            @Unique @Length(min="n", max="m") List this,
            Object newHead,
            @Positive int n, @Positive int m) {
        return this.first.head;
    }

    @JMLClause("ensures \\result == this.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique List this) {
        return this.size;
    }
}
