package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class List {

    public int head;
    public @Nullable @Length(min="size - 1", max="size - 1") List tail;

    public int size;

    // :: error: inconsistent.constructor.type
    public @Unique @Length(min="1", max="1") List(int head) {
        this.head = head;
        this.tail = null;
        this.size = 1;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    // :: error: inconsistent.constructor.type
    public @Unique @Length(min="tail.size + 1", max="tail.size + 1") List(int head, List tail) {
        this.head = head;
        this.tail = tail;
        this.size = tail == null ? 1 : tail.size + 1;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }

    @EnsuresLength(value="this", min="n+1", max="m+1")
    // :: error: contracts.postcondition.not.satisfied
    public void insert(
            @Unique @Length(min="n", max="m") List this,
            int newHead,
            int n, int m
    ) {
        Packing.unpack(this, List.class);
        // :: error: argument.type.incompatible
        this.tail = new List(head, tail);
        this.head = newHead;
        ++this.size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }
}
