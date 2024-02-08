import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

// :: error: inconsistent.constructor.type
class MutateOtherObjects {

    // :: error: initialization.field.uninitialized
    @Unique Foo foo;

    // :: error: contracts.postcondition.not.satisfied
    void mutate(@Unique MutateOtherObjects this, @Unique MutateOtherObjects other) {
        // :: error: initialization.write.committed.field
        this.foo = new Foo();

        Packing.unpack(this, MutateOtherObjects.class);
        this.foo = new Foo();
        Packing.pack(this, MutateOtherObjects.class);

        // :: error: assignment.invalid-lhs :: error: initialization.write.committed.field
        this.foo.i = 42;
        // :: error: assignment.invalid-lhs :: error: initialization.write.committed.field
        other.foo = new Foo();
    }
}
