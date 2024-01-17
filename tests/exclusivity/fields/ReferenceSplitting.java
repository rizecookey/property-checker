import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

// Test reference splitting rules for the Exclusivity Checker.
class ReferenceSplitting {

    // :: error: initialization.field.uninitialized
    @Unique Foo field;

    void refTransfer() {
        @ReadOnly Foo x;
        @Unique Foo a;

        x = new Foo();  // x is refined to @ExclMut
        a = x;          // x is updated to @ReadOnly
        // :: error: type.invalid
        this.field = x; // invalid, x is not @ExclMut anymore
    }
}
