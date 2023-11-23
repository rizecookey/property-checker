import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class MutateOtherObjects {
    @ExclMut Foo foo;

    void mutate(@ExclMut MutateOtherObjects this, @ExclMut MutateOtherObjects other) {
        this.foo = new Foo();
        // :: error: assignment.invalid-lhs
        this.foo.i = 42;
        // :: error: assignment.invalid-lhs
        other.foo = new Foo();
    }
}
