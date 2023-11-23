import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

// Test reference splitting rules for the Exclusivity Checker.
class References {

    void refNew() {
        @ReadOnly Foo x;
        x = new Foo();  // T-Ref-New
        @ExclMut Foo y;
        y = x;          // T-Ref-Transfer
    }

    void refCopyRo(@ExclMut Foo a) {
        @ReadOnly Foo x;
        @ReadOnly Foo y;
        @ReadOnly Foo z;

        // a stays @ExclMut for all of these
        x = a;
        y = a;
        z = a;
    }
}
