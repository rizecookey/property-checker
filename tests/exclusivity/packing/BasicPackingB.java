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
        this.isPackedToA();
        this.isUnpacked();
        this.isPackedToA();
        this.isFullyPacked();
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        // :: error: initialization.unpacking.unknown
    }

    void correctPackingCovariant(@UnknownInitialization(BasicPackingA.class) @Unique BasicPackingB this) {
        this.bField = new Obj();
        this.isFullyPacked();
    }

    // :: error: packing.postcondition.not.satisfied
    void returnTypeIncompatible(@Unique BasicPackingB this) {
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackNonReceiver(@Unique BasicPackingB this, @Unique BasicPackingB other) {
        // :: error: initialization.packing.nonreceiver
    }

    // :: error: packing.postcondition.not.satisfied
    void unpackAliased(@MaybeAliased BasicPackingB this) {
        // :: error: exclusivity.packing.aliased
    }

    void unpackObject(@Unique BasicPackingB this) {
        // :: error: initialization.unpacking.object.class
    }

    void incorrectModification(@Unique BasicPackingB this) {

        this.bField = null;


        // :: error: initialization.fields.uninitialized
    }

    void correctModification(@Unique BasicPackingB this) {

        this.bField = null;


        this.bField = new Obj();
    }

    void doublePacking0(@Unique BasicPackingB this) {
        // :: error: initialization.already.unpacked
        // :: error: initialization.already.packed
    }

    void doublePacking1(@Unique BasicPackingB this) {
        // :: error: initialization.already.unpacked
        // :: error: initialization.already.packed
    }
}
