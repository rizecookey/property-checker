import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import org.checkerframework.checker.initialization.qual.*;

class A {

    // :: error: initialization.field.uninitialized
    @Unique Object aField;
}

final class B extends A {

    // :: error: initialization.field.uninitialized
    @Unique Object bField;

    void foo(@Unique B this) {
        Packing.unpack(this, B.class);
        this.isPackedToA();
        Packing.unpack(this, A.class);
        this.isUnpacked();
        Packing.pack(this, A.class);
        this.isPackedToA();
        Packing.pack(this, B.class);
        this.isFullyPacked();
    }

    void isUnpacked(@Unique @UnderInitialization(Object.class) B this) {}
    void isPackedToA(@Unique @UnderInitialization(A.class) B this) {}
    void isPackedToB(@Unique @UnderInitialization(B.class) B this) {}
    void isFullyPacked(@Unique @UnderInitialization(B.class) B this) {}

    void bar(@Unique B this) {
        Packing.unpack(this, B.class);
        // :: error: initialization.already.unpacked
        Packing.unpack(this, B.class);
        Packing.pack(this, B.class);
        // :: error: initialization.already.packed
        Packing.pack(this, B.class);
    }

    void baz(@Unique B this) {
        Packing.unpack(this, B.class);
        this.field = null;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, B.class);
        this.field = new Object();
        Packing.pack(this, B.class);
    }
}
