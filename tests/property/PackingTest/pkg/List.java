package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class List {

    public int head;
    public @Nullable @Length(len="this.size - 1") List tail;

    public int size;

    @JMLClause("ensures this.head == head && this.tail == null && this.size == 1;")
    @JMLClause("assignable \\nothing;")
    // :: error: length.inconsistent.constructor.type
    public @Unique @Length(len="1") List(int head) {
        this.head = head;
        this.tail = null;
        this.size = 1;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @JMLClause("ensures this.head == head && this.tail == tail;")
    @JMLClause("assignable \\nothing;")
    // :: error: length.inconsistent.constructor.type :: error: length.contracts.postcondition.not.satisfied
    public @Unique @Length(len="n+1") List(int head, @Nullable @Length(len="n") List tail, int n) {
        this.head = head;
        this.tail = tail;
        this.size = tail == null ? 1 : tail.size + 1;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @EnsuresLength(value="this", len="n+1")
    @JMLClause("assignable this.*;")
    // :: error: length.contracts.postcondition.not.satisfied
    public void insert(
            @Unique @Length(len="n") List this,
            int newHead,
            int n
    ) {
        Packing.unpack(this, List.class);
        if (this.tail == null) {
            this.tail = new List(head);
        } else {
            // :: error: length.argument.type.incompatible
            this.tail = new List(this.head, this.tail, n - 1);
        }
        this.head = newHead;
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }
}
