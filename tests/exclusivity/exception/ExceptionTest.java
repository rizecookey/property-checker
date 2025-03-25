import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ExceptionTest {

    public @Unique Object field;

    // :: error: simple.inconsistent.constructor.type
    public @B ExceptionTest() {
        this.field = new Object();
    }

    public void foo(@Unique @B ExceptionTest this) {}

    public static void main() {
        @B ExceptionTest obj = new ExceptionTest();
        try {
            obj.foo();
        } catch (Exception e) {
            // :: error: packing.method.invocation.invalid :: error: simple.method.invocation.invalid
            obj.foo();
        }
    }
}
