import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Bar {

    public void change(@Unique Bar this) {}
}

class Foo {
    @ReadOnly Bar readOnly;
    @MaybeAliased Bar aliased;
    // :: error: initialization.field.uninitialized
    @Unique Bar unique;

    public void foo(@ReadOnly Foo this) {
        // :: error: exclusivity.type.invalidated
        this.unique.change();
    }

    public @ReadOnly Bar getReadOnly(@ReadOnly Foo this) {
        return readOnly;
    }

    public @ReadOnly Bar getReadOnlyFake(@ReadOnly Foo this) {
        // :: error: exclusivity.type.invalidated
        this.unique.change();
        // :: error: exclusivity.type.invalidated
        this.aliased.change();
        // :: error: exclusivity.type.invalidated
        this.readOnly.change();
        return readOnly;
    }

    public @Unique Bar getUniqueFromReadOnly(@ReadOnly Foo this) {
        // :: error: exclusivity.type.invalidated
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromReadOnly(@ReadOnly Foo this) {
        return aliased;
    }

    public @Unique Bar getUniqueFromAliasedWrong(@MaybeAliased Foo this) {
        // :: error: exclusivity.type.invalidated
        return unique;
    }

    public @MaybeAliased Bar getUniqueFromAliasedRight(@MaybeAliased Foo this) {
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromAliased(@MaybeAliased Foo this) {
        return aliased;
    }

    public @Unique Bar getUniqueFromUnique(@Unique Foo this) {
        // The adapted field type is compatible with the result type, we we're not allowed to leak a unique field
        // :: error: exclusivity.type.invalidated
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromUnique(@Unique Foo this) {
        return aliased;
    }
}
