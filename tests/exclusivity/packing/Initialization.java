import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import org.checkerframework.dataflow.qual.*;

class NonFinalClass {
    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    NonFinalClass() {
        this.unique = new Object();
        // :: error: method.invocation.invalid
        this.foo();
    }

    NonFinalClass(int dummy) {
        this.unique = new Object();

        Packing.pack(this, NonFinalClass.class);
        // :: error: method.invocation.invalid
        this.foo();
    }

    @Pure
    @EnsuresUnique("this")
    void foo(@Unique NonFinalClass this) {}
}

final class FinalClass {
    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    FinalClass() {
        this.unique = new Object();
        // :: error: method.invocation.invalid
        this.foo();
    }

    FinalClass(int dummy) {
        this.unique = new Object();

        Packing.pack(this, FinalClass.class);
        this.foo();
    }

    @Pure
    @EnsuresUnique("this")
    void foo(@Unique FinalClass this) {}
}
