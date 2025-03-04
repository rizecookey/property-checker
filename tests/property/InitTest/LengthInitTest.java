import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public abstract class LengthInitTest {
    
    public @MaybeAliased @Length(len="1") List i2;
    public @MaybeAliased @Length(len="1") List i3;
    public @MaybeAliased @Length(len="2") List i4;

    // These constructor checks fail because the assignment of any field leads to the invalidation of all
    // @Length types (@Length is defined in terms of a method call to size(), and refinements with method calls
    // are invalidated when any field changes)

    // :: error: length.contracts.postcondition.not.satisfied
    public LengthInitTest(@MaybeAliased @Length(len="1") List arg) {
        i2 = arg;
        i3 = arg;

        // :: error: length.assignment.type.incompatible
        @Length(len="1") List l3 = arg;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, LengthInitTest.class);
    }

    // :: error: length.contracts.postcondition.not.satisfied
    public LengthInitTest(@MaybeAliased @Length(len="1") List arg, int dummy) {
        i2 = arg;
        i3 = arg;
        i4 = arg;

        // :: error: length.assignment.type.incompatible
        @Length(len="2") List l3 = arg;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, LengthInitTest.class);
    }
}
