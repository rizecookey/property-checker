import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class MutateOtherObjects {
    @Unique Foo foo;

    void mutate(@Unique MutateOtherObjects this, @Unique MutateOtherObjects other) {
        this.foo = new Foo();
        // :: error: assignment.invalid-lhs
        this.foo.i = 42;
        // :: error: assignment.invalid-lhs
        other.foo = new Foo();
    }
}
