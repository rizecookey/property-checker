import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class MethodCall {

    @ReadOnly @UnknownInitialization(Object.class) @Nullable Foo field;

    MethodCall() {
    }

    @NonMonotonic
    void mthRO(@UnknownInitialization @ReadOnly MethodCall this) {}

    @NonMonotonic
    void mthUnique(@UnknownInitialization @Unique MethodCall this) {}

    @NonMonotonic
    void mthMA(@UnknownInitialization @MaybeAliased MethodCall this) {}

    @NonMonotonic
    void mthParam(@UnknownInitialization @MaybeAliased MethodCall this, @UnknownInitialization @MaybeAliased @Nullable Foo arg) {}

    @Unique Foo mthret(@MaybeAliased MethodCall this) {
        return new Foo();
    }

    @NonMonotonic
    @EnsuresUnknownInit(targetValue=Object.class)
    void invoke(@MaybeAliased MethodCall this) {
        @ReadOnly Foo x;
        @Unique Foo a;
        x = new Foo();   // x is refined to @Unique
        x.mthUnique();
        this.mthParam(x);     // x is refined to @MaybeAliased
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        x.mthUnique();     // invalid, x is not @Unique anymore
    }

    @NonMonotonic
    // :: error: exclusivity.postcondition.not.satisfied
    void invokeAssign(@Unique MethodCall this) {
        @Unique Foo b;
        b = this.mthret();
    }

    @NonMonotonic
    void invalidate1(@Unique MethodCall this) {
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.field.mthUnique();
        this.mthUnique();
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid :: error: nullness.dereference.of.nullable
        this.field.mthUnique(); // invalid, refinement of field has been forgotten
    }

    @NonMonotonic
    void dontInvalidate(@Unique MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthRO();
        a = this.field; // still valid, since we control all access to this
    }
}
