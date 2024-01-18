import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Foo {
    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    Foo() {
        this.foo(this.unique);
    }

    Foo(int dummy) {
        this.unique = new Object();
        this.foo(this.unique);
    }

    void foo(@Unique Foo this, @Unique Object bar) {}
}
