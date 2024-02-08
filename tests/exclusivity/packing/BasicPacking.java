import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class Obj {

    // :: error: inconsistent.constructor.type
    @NonNull Obj() {

        Packing.pack(this, Obj.class);
    }
}

class A {

    @Unique Object aField;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop A() {
        aField = new Obj();
        Packing.pack(this, A.class);
    }
}

final class B extends A {

    @Unique Object bField;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop B() {
        bField = new Obj();
        Packing.pack(this, B.class);
    }

    @Pure
    void isUnpacked(@Unique @UnderInitialization(Object.class) B this) {}

    @Pure
    void isPackedToA(@Unique @UnderInitialization(A.class) B this) {}

    @Pure
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

    // :: error: contracts.postcondition.not.satisfied
    void unpackingCovariant(@UnknownInitialization(A.class) @Unique B this) {
        // :: error: initialization.unpacking.unknown
        Packing.unpack(this, A.class);
    }

    void correctPackingCovariant(@UnknownInitialization(A.class) @Unique B this) {
        this.bField = new Obj();
        Packing.pack(this, B.class);
        this.isFullyPacked();
    }

    // :: error: contracts.postcondition.not.satisfied
    void returnTypeIncompatible(@Unique B this) {
        Packing.unpack(this, B.class);
    }

    // :: error: contracts.postcondition.not.satisfied
    void unpackNonReceiver(@Unique B this, @Unique B other) {
        // :: error: initialization.packing.nonreceiver
        Packing.unpack(other, B.class);
    }

    // :: error: contracts.postcondition.not.satisfied
    void unpackAliased(@MaybeAliased B this) {
        // :: error: exclusivity.packing.aliased
        Packing.unpack(this, B.class);
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

        this.bField = new Obj();
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
        Packing.pack(this, B.class);
    }
}
