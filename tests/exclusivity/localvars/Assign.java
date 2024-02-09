import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

// :: error: inconsistent.constructor.type
final class Assign {

    // :: error: initialization.field.uninitialized
    @Unique Foo foo;
    // :: error: exclusivity.type.invalidated :: error: initialization.field.uninitialized
    @ExclBottom Foo bar;

    void assignWritableThis(@Unique Assign this) {
        Packing.unpack(this, Assign.class);
        this.foo = new Foo();
        Packing.pack(this, Assign.class);
    }

    void assignParam(@Unique Assign this, @Unique Assign other) {
        // :: error: assignment.parameter
        other = new Assign();
    }
}
