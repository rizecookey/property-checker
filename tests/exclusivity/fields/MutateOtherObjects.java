import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class MutateOtherObjects {

    // :: error: initialization.field.uninitialized
    @Dependable @Unique Foo foo;

    @NonMonotonic
    void mutate(@Unique MutateOtherObjects this, @Unique MutateOtherObjects other) {
        this.foo = new Foo();

        // :: error: assignment.invalid-lhs :: error: initialization.write.committed.field
        this.foo.i = 42;
        // :: error: assignment.invalid-lhs :: error: initialization.write.committed.field
        other.foo = new Foo();
    }
}
