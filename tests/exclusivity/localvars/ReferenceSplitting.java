import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

// Test reference splitting rules for the Exclusivity Checker.
class ReferenceSplitting {

    void splitMut() {
        @ReadOnly Foo x;
        @MaybeAliased Foo a;
        @MaybeAliased Foo b;
        x = new Foo();      // x is refined to @ExclMut
        a = x;              // x is updated to @ShrMut
        // :: error: type.invalid
        b = x;              // invalid, x is not @ExclMut anyomre
    }

    void splitMut0() {
        @ReadOnly Foo x = new Foo();
        @MaybeAliased Foo a = x;
        // :: error: type.invalid
        @MaybeAliased Foo b = x;
    }

    void splitMut1() {
        @ReadOnly Foo x; x = new Foo();
        @ShrMut Foo a; a = x;
        @MaybeAliased Foo b;
        // :: error: type.invalid
        b = x;
    }

    void splitImmut() {
        @ReadOnly Foo x;
        @MaybeAliased Foo a;
        @MaybeAliased Foo b;
        x = new Foo();      // x is refined to @ExclMut
        a = x;              // x is updated to @Immut
        // :: error: type.invalid
        b = x;              // invalid, x is not @ExclMut anyomre
    }

    void refTransfer() {
        @ReadOnly Foo x;
        @Unique Foo a;
        @MaybeAliased Foo b;
        @MaybeAliased Foo c;

        x = new Foo();  // x is refined to @ExclMut
        a = x;          // x is updated to @ReadOnly
        // :: error: type.invalid
        b = x;          // invalid, x is not @ExclMut anymore
        // :: error: type.invalid
        c = x;          // invalid, x is not @ExclMut anymore
    }
}
