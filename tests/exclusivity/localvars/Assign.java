import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Assign {

    // :: error: initialization.field.uninitialized
    @Unique Foo foo;
    // :: error: exclusivity.type.invalidated :: error: initialization.field.uninitialized
    @ExclBottom Foo bar;

    void assignReadOnlyThis(@ReadOnly Assign this) {
        // :: error: assignment.this-not-writable
        this.foo = new Foo();
    }

    void assignWritableThis(@Unique Assign this) {
        this.foo = new Foo();
    }
}
