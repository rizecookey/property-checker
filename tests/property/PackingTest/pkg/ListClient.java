package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class ListClient {

    @Unique @Length(min="1", max="6") List a;
    @MaybeAliased @Length(min="1", max="1") List b;
    @Unique @Length(min="a.size", max="a.size") List c;

    public ListClient() {
        this.a = new List(42);
        this.b = new List(42);
        this.c = new List(42);

        // :: error: initialization.fields.uninitialized)
        Packing.pack(this, ListClient.class);
    }

    void correctPacking(@Unique ListClient this) {
        Packing.unpack(this, ListClient.class);
        // :: error: method.invocation.invalid
        a.insert(42, 1, 6);
        // :: error: method.invocation.invalid
        c.insert(42, 1, 6);
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, ListClient.class);
    }
}
