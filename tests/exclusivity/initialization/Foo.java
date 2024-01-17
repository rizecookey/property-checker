import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Foo {
    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    Foo() {
        // :: error: method.invocation.invalid
        foo(unique);
        unique = new Object();
        foo(unique);
    }

    void foo(@Unique Object bar) {}
}
