package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class PackingThisTest {

    public @MaybeAliased PackingThisTest(PackingThisTest other) {
        unknownInit();
    }

    public void lateInit(@UnknownInitialization(PackingThisTest.class) PackingThisTest this) {
        lateInitHelper();
        staticMethod(this);
    }

    @EnsuresInitialized("this")
    // :: error: packing.postcondition.not.satisfied
    public void lateInitHelper(@UnknownInitialization(PackingThisTest.class) PackingThisTest this) {}

    public void unknownInit(@UnknownInitialization(PackingThisTest.class) PackingThisTest this) {
        // :: error: packing.argument.type.incompatible
        staticMethod(this);
    }

    public void init0() {
        staticMethod(this);
    }
    public void init1() {
        new PackingThisTest(this);
    }
    public void init2(PackingThisTest other) {
        other.init2(this);
    }
    public void init3(PackingThisTest other) {
        other.init0();
        other.lateInit();

        other.init2(other);
        staticMethod(other);
        new PackingThisTest(other);

        other.init2(this);
        staticMethod(this);
        new PackingThisTest(this);
    }

    public static void staticMethod(PackingThisTest arg) {}
}
