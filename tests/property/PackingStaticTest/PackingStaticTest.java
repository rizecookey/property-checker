package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class PackingStaticTest {

    public static PackingStaticTest instance = new PackingStaticTest();

    private Object field = new Object();

    public static void staticMethod() {
        instance.field.toString();
    }

    public void objectMethod() {
        instance.field.toString();
    }
}
