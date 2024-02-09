import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public abstract class LengthInitTest {
    
    public @MaybeAliased @Length(min="1", max="3") List i2;
    public @MaybeAliased @Length(min="1", max="1") List i3;
    public @MaybeAliased @Length(min="1", max="3") List i4;

    public LengthInitTest(@MaybeAliased @Length(min="1", max="3") List arg) {
        i2 = arg;

        i3 = arg;

        // :: error: assignment.type.incompatible
        @Length(min="1", max="1") List l3 = arg;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, LengthInitTest.class);
    }
}
