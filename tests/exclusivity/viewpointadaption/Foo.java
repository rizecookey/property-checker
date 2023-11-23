import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Bar {

    public void change(@ExclMut Bar this) {}
}

class Foo {
    @ReadOnly Bar ro;
    @ShrMut Bar shrMut;
    @Immutable Bar immut;
    @ExclMut Bar exclMut;

    public @ReadOnly Bar getRO(@ReadOnly Foo this) {
        return ro;
    }

    public @ReadOnly Bar getROFake(@ReadOnly Foo this) {
        // :: error: type.invalid
        this.exclMut.change();
        // :: error: type.invalid
        this.shrMut.change();
        return ro;
    }

    public @ExclMut Bar getExclMutFromRO(@ReadOnly Foo this) {
        // :: error: type.invalid
        return exclMut;
    }

    public @ExclMut Bar getExclMutFromShrMut(@ShrMut Foo this) {
        // :: error: type.invalid
        return exclMut;
    }
}
