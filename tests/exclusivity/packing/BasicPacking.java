import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class A {

    // :: error: initialization.field.uninitialized
    @Unique Object aField;
}

final class B extends A {

    // :: error: initialization.field.uninitialized
    @Unique Object bField;

    @Pure
    void isUnpacked(@Unique @UnderInitialization(Object.class) B this) {}

    @Pure
    @EnsuresUnderInit(targetValue=A.class)
    @EnsuresUnique
    void isPackedToA(@Unique @UnderInitialization(A.class) B this) {}

    @Pure
    @EnsuresUnderInit(targetValue=B.class)
    @EnsuresUnique
    void isPackedToB(@Unique @UnderInitialization(B.class) B this) {}

    @Pure
    void isFullyPacked(@Unique @Initialized B this) {}

    @Pure
    void isPackedToAtLeastObject(@Unique @UnknownInitialization(Object.class) B this) {}

    @Pure
    void isPackedToPackedToAtLeastA(@Unique @UnknownInitialization(A.class) B this) {}

    void correctPacking(@Unique B this) {
        Packing.unpack(this, B.class);
        this.isPackedToA();
        Packing.unpack(this, A.class);
        this.isUnpacked();
        Packing.pack(this, A.class);
        this.isPackedToA();
        Packing.pack(this, B.class);
        this.isFullyPacked();
    }

    void correctPackingCovariant(@UnknownInitialization(A.class) @Unique B this) {
        Packing.unpack(this, A.class);
        this.isPackedToAtLeastObject();
        Packing.pack(this, A.class);
        this.isPackedToPackedToAtLeastA();
        Packing.pack(this, B.class);
        this.isFullyPacked();
    }

    void unpackNonReceiver(@Unique B this, @Unique B other) {
        // :: error: initialization.packing.nonreceiver
        Packing.unpack(other, B.class);
    }

    void unpackObject(@Unique B this) {
        // :: error: initialization.unpacking.object.class
        Packing.unpack(this, Object.class);
    }

    void incorrectModification(@Unique B this) {
        Packing.unpack(this, A.class);

        this.bField = null;

        Packing.pack(this, A.class);

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, B.class);
    }

    void correctModification(@Unique B this) {
        Packing.unpack(this, A.class);

        this.bField = null;

        Packing.pack(this, A.class);

        this.bField = new Object();
        Packing.pack(this, B.class);
    }

    void doublePacking0(@Unique B this) {
        Packing.unpack(this, B.class);
        // :: error: initialization.already.unpacked
        Packing.unpack(this, B.class);
        Packing.pack(this, B.class);
        // :: error: initialization.already.packed
        Packing.pack(this, B.class);
    }

    void doublePacking1(@Unique B this) {
        Packing.unpack(this, A.class);
        // :: error: initialization.already.unpacked
        Packing.unpack(this, B.class);
        Packing.pack(this, B.class);
        // :: error: initialization.already.packed
        Packing.pack(this, A.class);
    }
}
