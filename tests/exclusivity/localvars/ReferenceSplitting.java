import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

// Test reference splitting rules for the Exclusivity Checker.
class ReferenceSplitting {

    void split() {
        @ReadOnly Foo x;
        @MaybeAliased Foo a;
        @MaybeAliased Foo b;
        x = new Foo();      // x is refined to @Unique
        a = x;              // x is updated to @MaybeAliased
        b = x;
    }

    void split0() {
        @ReadOnly Foo x = new Foo();
        @MaybeAliased Foo a = x;
        @MaybeAliased Foo b = x;
    }

    void split1() {
        @ReadOnly Foo x;
        x = new Foo();
        @MaybeAliased Foo a;
        a = x;
        @MaybeAliased Foo b;
        b = x;
    }

    void refTransfer() {
        @ReadOnly Foo x;
        @Unique Foo a;
        @MaybeAliased Foo b;
        @MaybeAliased Foo c;

        x = new Foo();  // x is refined to @Unique
        a = x;          // x is updated to @ReadOnly
        // :: error: exclusivity.type.invalidated
        b = x;          // invalid, x is not @Unique anymore
        c = x;          // valid, x is not @ExclBottom
    }
}
