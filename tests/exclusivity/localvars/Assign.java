import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Assign {
    @ExclMut Foo foo;
    // :: error: type.invalid
    @ExclusivityBottom Foo bar;

    void assignReadOnlyThis(@ReadOnly Assign this) {
        // :: error: assignment.this-not-writable
        this.foo = new Foo();
    }

    void assignWritableThis(@ExclMut Assign this) {
        this.foo = new Foo();
    }
}
