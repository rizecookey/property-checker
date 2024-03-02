import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class BasicPackingB extends BasicPackingA {

    @Unique Object bField;

    BasicPackingB() {
        this.bField = new Obj();
        Packing.pack(this, BasicPackingB.class);
    }

    @Pure
    void isUnpacked(@Unique @UnderInitialization(Object.class) BasicPackingB this) {}

    @Pure
    void isPackedToA(@Unique @UnderInitialization(BasicPackingA.class) BasicPackingB this) {}

    @Pure
    void isPackedToB(@Unique @UnderInitialization(BasicPackingB.class) BasicPackingB this) {}

    @Pure
    void isFullyPacked(@Unique @Initialized BasicPackingB this) {}

    @Pure
    void isPackedToAtLeastObject(@Unique @UnknownInitialization(Object.class) BasicPackingB this) {}

    @Pure
    void isPackedToPackedToAtLeastA(@Unique @UnknownInitialization(BasicPackingA.class) BasicPackingB this) {}

    void correctPacking(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingB.class);
        this.isPackedToA();
        Packing.unpack(this, BasicPackingA.class);
        this.isUnpacked();
        Packing.pack(this, BasicPackingA.class);
        this.isPackedToA();
        Packing.pack(this, BasicPackingB.class);
        this.isFullyPacked();
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        // :: error: initialization.unpacking.unknown
        Packing.unpack(this, BasicPackingA.class);
    }

    void correctPackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        this.bField = new Obj();
        Packing.pack(this, BasicPackingB.class);
        this.isFullyPacked();
    }

    // :: error: packing.postcondition.not.satisfied
    void returnTypeIncompatible(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingB.class);
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackNonReceiver(@Unique BasicPackingB this, @Unique BasicPackingB other) {
        // :: error: initialization.packing.nonreceiver
        Packing.unpack(other, BasicPackingB.class);
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackAliased(@MaybeAliased BasicPackingB this) {
        // :: error: exclusivity.packing.aliased
        Packing.unpack(this, BasicPackingB.class);
    }

    void unpackObject(@Unique BasicPackingB this) {
        // :: error: initialization.unpacking.object.class
        Packing.unpack(this, Object.class);
    }

    void incorrectModification(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingA.class);

        this.bField = null;

        Packing.pack(this, BasicPackingA.class);

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, BasicPackingB.class);
    }

    void correctModification(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingA.class);

        this.bField = null;

        Packing.pack(this, BasicPackingA.class);

        this.bField = new Obj();
        Packing.pack(this, BasicPackingB.class);
    }

    void doublePacking0(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingB.class);
        // :: error: initialization.already.unpacked
        Packing.unpack(this, BasicPackingB.class);
        Packing.pack(this, BasicPackingB.class);
        // :: error: initialization.already.packed
        Packing.pack(this, BasicPackingB.class);
    }

    void doublePacking1(@Unique BasicPackingB this) {
        Packing.unpack(this, BasicPackingA.class);
        // :: error: initialization.already.unpacked
        Packing.unpack(this, BasicPackingB.class);
        Packing.pack(this, BasicPackingB.class);
        // :: error: initialization.already.packed
        Packing.pack(this, BasicPackingA.class);
        Packing.pack(this, BasicPackingB.class);
    }
}
