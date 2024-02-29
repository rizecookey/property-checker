import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class ReferenceSplitting {

    // :: error: initialization.field.uninitialized
    @Unique Foo field;

    void refTransfer() {
        @ReadOnly @NullTop Foo x;
        @Unique @NullTop Foo a;

        x = new Foo();  // x is refined to @ExclMut
        a = x;          // x is updated to @ReadOnly
        // :: error: exclusivity.type.invalidated :: error: initialization.write.committed.field
        this.field = x; // invalid, x is not @ExclMut anymore
    }
}
