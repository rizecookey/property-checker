import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Bar {

    public void change(@Unique Bar this) {}
}

class Foo {
    @ReadOnly Bar ro;
    @MaybeAliased Bar shrMut;
    @MaybeAliased Bar immut;
    @Unique Bar unique;

    public @ReadOnly Bar getRO(@ReadOnly Foo this) {
        return ro;
    }

    public @ReadOnly Bar getROFake(@ReadOnly Foo this) {
        // :: error: type.invalid
        this.unique.change();
        // :: error: type.invalid
        this.shrMut.change();
        return ro;
    }

    public @Unique Bar getUniqueFromRO(@ReadOnly Foo this) {
        // :: error: type.invalid
        return unique;
    }

    public @Unique Bar getUniqueFromShrMut(@MaybeAliased Foo this) {
        // :: error: type.invalid
        return unique;
    }
}
