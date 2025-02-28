import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class Foo {

    int i;

    Foo() {
    }

    @NonMonotonic
    public void mth(@ReadOnly @UnknownInitialization(Object.class) Foo this) {}

    @NonMonotonic
    public void mthUnique(@Unique Foo this) {}
}
