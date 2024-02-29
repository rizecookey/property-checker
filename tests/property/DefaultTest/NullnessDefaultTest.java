import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class NullnessDefaultTest {

    // :: error: initialization.field.uninitialized
    @NonNull Object nonNullField;
    // :: error: initialization.field.uninitialized
    @Nullable Object nullableField;
    // :: error: initialization.field.uninitialized
    Object defaultField;
    
    // :: error: initialization.field.uninitialized :: error: nullness.type.invalid.abstract.state
    @ReadOnly @NonNull Object nonNullField0;
    // :: error: initialization.field.uninitialized :: error: nullness.type.invalid.abstract.state
    @ReadOnly Object defaultField0;

    public void foo() {
        @NonNull Object nonNullLocal = nonNullField;
        nonNullLocal = defaultField;
        // :: error: nullness.assignment.type.incompatible
        nonNullLocal = nullableField;
        
        @Nullable Object nullableLocal = nonNullField;
        nullableLocal = defaultField;
        nullableLocal = nullableField;
        
        Object defaultLocal = nonNullField;
        defaultLocal = defaultField;
        defaultLocal = nullableField;
    }

    public void validParam0(@NonNull Object arg) {}
    public void validParam1(Object arg) {}

    // :: error: nullness.type.invalid.abstract.state
    public void invalidParam0(@ReadOnly @NonNull Object arg) {}
    // :: error: nullness.type.invalid.abstract.state
    public void invalidParam1(@ReadOnly Object arg) {}
}
