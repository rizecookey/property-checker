import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class ReferenceSplitting {

    // :: error: initialization.field.uninitialized
    @Unique Foo field;

    // :: error: initialization.fields.uninitialized
    void refTransfer(@Unique ReferenceSplitting this) {
        @ReadOnly @NullTop Foo x;
        @Unique @NullTop Foo a;

        x = new Foo();  // x is updated to @Unique
        a = x;          // x is updated to @ReadOnly
        // :: error: initialization.nonmonotonic.write
        this.field = x; // invalid, x is not @Unique anymore
    }
}
