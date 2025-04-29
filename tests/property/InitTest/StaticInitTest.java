import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class StaticInitTest {
    
    static int unannotated;
    static @Remainder(remainder="0", modulus="2") int even = 2;
    static @Remainder(remainder="1", modulus="2") int odd = 1;
    static Object obj = new Object();
    static String str = "aaa";

    public static @Remainder(remainder="0", modulus="2") int foo(StaticInitTest a) {
        a.bar();
        obj.toString();
        str.toString();
    	return even;
    }

    public void bar() {}
}
