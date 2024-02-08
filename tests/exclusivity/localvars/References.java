import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

// :: error: inconsistent.constructor.type
class References {

    void refNew() {
        @ReadOnly Foo x;
        x = new Foo();  // T-Ref-New
        @Unique Foo y;
        y = x;          // T-Ref-Transfer
    }

    void refCopyRo(@Unique Foo a) {
        @ReadOnly Foo x;
        @ReadOnly Foo y;
        @ReadOnly Foo z;

        // a stays @Unique for all of these
        x = a;
        y = a;
        z = a;
    }
}
