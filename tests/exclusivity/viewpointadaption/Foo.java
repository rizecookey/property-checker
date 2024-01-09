import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Bar {

    public void change(@Unique Bar this) {}
}

class Foo {
    @ReadOnly Bar readOnly;
    @MaybeAliased Bar aliased;
    @Unique Bar unique;

    public void foo(@ReadOnly Foo this) {
        // :: error: type.invalid
        this.unique.change();
    }

    public @ReadOnly Bar getReadOnly(@ReadOnly Foo this) {
        return readOnly;
    }

    public @ReadOnly Bar getReadOnlyFake(@ReadOnly Foo this) {
        // :: error: type.invalid
        this.unique.change();
        // :: error: type.invalid
        this.aliased.change();
        // :: error: type.invalid
        this.readOnly.change();
        return readOnly;
    }

    public @Unique Bar getUniqueFromReadOnly(@ReadOnly Foo this) {
        // :: error: type.invalid
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromReadOnly(@ReadOnly Foo this) {
        return aliased;
    }

    public @Unique Bar getUniqueFromAliased(@MaybeAliased Foo this) {
        // :: error: type.invalid
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromAliased(@MaybeAliased Foo this) {
        return aliased;
    }

    public @Unique Bar getUniqueFromUnique(@Unique Foo this) {
        // The adapted field type is compatible with the result type, we we're not allowed to leak a unique field
        // :: error: type.invalid
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromUnique(@Unique Foo this) {
        return aliased;
    }
}
