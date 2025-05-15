package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class PackingNewTest {

    public @MaybeAliased PackingNewTest() {}

    public void method() {}

    public static void staticMethod(PackingNewTest obj) {}

    public static void createNew() {
        new PackingNewTest().method();
        staticMethod(new PackingNewTest());
    }

    public static void createNewAnon() {
        (new PackingNewTest() {}).method();
        staticMethod(new PackingNewTest() {});
    }
}
