import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Assign {
    @Unique Foo foo;
    // :: error: type.invalid
    @ExclBottom Foo bar;

    void assignReadOnlyThis(@ReadOnly Assign this) {
        // :: error: assignment.this-not-writable
        this.foo = new Foo();
    }

    void assignWritableThis(@Unique Assign this) {
        this.foo = new Foo();
    }
}
