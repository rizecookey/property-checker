import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import pkg.List;

public final class ListClient {

    @Unique  @Length(min="1", max="6") List a;
    @MaybeAliased @Length(min="5", max="5") List b;
    @Unique @Length(min="a.size", max="a.size") List c;

    void correctPacking() {
        Packing.unpack(this, ListClient.class);
        a.insert(42, 1, 6);
        c.insert(42, 1, 6);
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, ListClient.class);
    }
}
