import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class Foo {

    int i;

    @NonNull Foo() {
        Packing.pack(this, Foo.class);
    }

    public void mth(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {}

    public void mthUnique(@Unique @NullTop Foo this) {}
}
