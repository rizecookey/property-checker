import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class InitializationFinalClass {
    @ReadOnly @UnknownInitialization(Object.class) @NullTop Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    InitializationFinalClass() {
        this.unique = new Obj();
        // :: error: initialization.fields.uninitialized
        this.foo();
    }

    InitializationFinalClass(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();

        this.foo();
    }

    @Pure
    void foo(@Unique @NullTop InitializationFinalClass this) {}
}
