import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class Bar {

    public void change(@Unique @NullTop Bar this) {}
}

// :: error: inconsistent.constructor.type
class Foo {
    @ReadOnly @NullTop Bar readOnly;
    // :: error: initialization.field.uninitialized
    @MaybeAliased Bar aliased;
    // :: error: initialization.field.uninitialized
    @Unique Bar unique;

    public void foo(@ReadOnly @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated
        this.unique.change();
    }

    public @ReadOnly @NullTop Bar getReadOnly(@ReadOnly @NullTop Foo this) {
        return readOnly;
    }

    public @ReadOnly @NullTop Bar getReadOnlyFake(@ReadOnly @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated
        this.unique.change();
        // :: error: exclusivity.type.invalidated
        this.aliased.change();
        // :: error: exclusivity.type.invalidated
        this.readOnly.change();
        // :: error: exclusivity.type.invalidated
        return readOnly;
    }

    public @Unique @NullTop Bar getUniqueFromReadOnly(@ReadOnly @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated
        return unique;
    }

    public @MaybeAliased Bar getAliasedFromReadOnly(@ReadOnly @NullTop Foo this) {
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
