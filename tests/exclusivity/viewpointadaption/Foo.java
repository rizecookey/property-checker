import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class Foo {
    @ReadOnly @UnknownInitialization(Object.class) @NullTop Bar readOnly;
    // :: error: initialization.field.uninitialized
    @MaybeAliased Bar aliased;
    // :: error: initialization.field.uninitialized
    @Unique Bar unique;

    public void foo(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        this.unique.change();
    }

    public @ReadOnly @UnknownInitialization(Object.class) @NullTop Bar getReadOnly(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {
        return this.readOnly;
    }

    public @ReadOnly @UnknownInitialization(Object.class) @NullTop Bar getReadOnlyFake(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        this.unique.change();
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        this.aliased.change();
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        this.readOnly.change();
        // :: error: exclusivity.type.invalidated
        return this.readOnly;
    }

    public @Unique @NullTop Bar getUniqueFromReadOnly(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated :: error: packing.return.type.incompatible
        return this.unique;
    }

    public @MaybeAliased Bar getAliasedFromReadOnly(@ReadOnly @UnknownInitialization(Object.class) @NullTop Foo this) {
        // :: error: exclusivity.type.invalidated :: error: nullness.return.type.incompatible :: error: packing.return.type.incompatible
        return this.aliased;
    }

    public @Unique Bar getUniqueFromAliasedWrong(@MaybeAliased Foo this) {
        // :: error: exclusivity.type.invalidated
        return this.unique;
    }

    public @MaybeAliased Bar getUniqueFromAliasedRight(@MaybeAliased Foo this) {
        return this.unique;
    }

    public @MaybeAliased Bar getAliasedFromAliased(@MaybeAliased Foo this) {
        return this.aliased;
    }

    // The adapted field type is compatible with the result type, but we're not allowed to leak a unique field
    // :: error: initialization.fields.uninitialized
    public @Unique Bar getUniqueFromUnique(@Unique Foo this) {
        return this.unique;
    }

    public @MaybeAliased Bar getAliasedFromUnique(@Unique Foo this) {
        return this.aliased;
    }
}
