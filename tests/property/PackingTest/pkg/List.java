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

    public @Length(min="tail.size + 1", max="tail.size + 1") List(int head, List tail) {
        this.head = head;
        this.next = next;
        size = next == null ? 1 : next.size + 1;
        Packing.pack(this, List.class);
    }

    // :: error: contracts.postcondition.not.satisfied
    @EnsuresLength(value="this", min="n+1", max="m+1")
    public void insert(
            @Length(min="n", max="m") List this,
            int newHead,
            int n, int m
    ) {
        Packing.unpack(this, List.class);
        tail = new List(head, tail);
        head = newHead;
        ++size;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, List.class);
    }
}
