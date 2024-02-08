import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class NonFinalClass {
    @ReadOnly @NullTop Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop @Initialized NonFinalClass() {
        this.unique = new Obj();
        // :: error: method.invocation.invalid
        this.foo();
    }

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop @Initialized NonFinalClass(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();
        Packing.pack(this, NonFinalClass.class);

        // :: error: method.invocation.invalid
        this.foo();
    }

    @Pure
    void foo(@Unique NonFinalClass this) {}
}

final class FinalClass {
    @ReadOnly @NullTop Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop FinalClass() {
        this.unique = new Obj();
        // :: error: method.invocation.invalid
        this.foo();
    }

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop FinalClass(int dummy) {
        this.aliased = new Obj();
        this.unique = new Obj();

        Packing.pack(this, FinalClass.class);
        this.foo();
    }

    @Pure
    void foo(@Unique @NullTop FinalClass this) {}
}
