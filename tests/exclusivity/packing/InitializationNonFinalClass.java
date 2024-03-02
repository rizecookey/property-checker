import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class InitializationNonFinalClass {
    @ReadOnly @NullTop Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    @Initialized InitializationNonFinalClass() {
        this.unique = new Obj();
        // :: error: nullness.method.invocation.invalid :: error: packing.method.invocation.invalid
        this.foo();
    }

    @Initialized InitializationNonFinalClass(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();
        Packing.pack(this, InitializationNonFinalClass.class);

        // :: error: nullness.method.invocation.invalid :: error: packing.method.invocation.invalid
        this.foo();
    }

    @Pure
    void foo(@Unique InitializationNonFinalClass this) {}
}
