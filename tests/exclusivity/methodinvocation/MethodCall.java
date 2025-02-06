import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class MethodCall {

    @ReadOnly @UnknownInitialization(Object.class) @NullTop Foo field;

    @NullTop MethodCall() {
    }

    void mthRO(@UnknownInitialization @ReadOnly @NullTop MethodCall this) {}

    void mthUnique(@UnknownInitialization @Unique @NullTop MethodCall this) {}

    void mthMA(@UnknownInitialization @MaybeAliased @NullTop MethodCall this) {}

    void mthParam(@UnknownInitialization @MaybeAliased @NullTop MethodCall this, @UnknownInitialization @MaybeAliased @NullTop Foo arg) {}

    @Unique Foo mthret(@MaybeAliased @NullTop MethodCall this) {
        return new Foo();
    }

    @EnsuresUnknownInit(targetValue=Object.class)
    void invoke(@MaybeAliased @NullTop MethodCall this) {
        @ReadOnly Foo x;
        @Unique Foo a;
        x = new Foo();   // x is refined to @Unique
        x.mthUnique();
        this.mthParam(x);     // x is refined to @MaybeAliased
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        x.mthUnique();     // invalid, x is not @Unique anymore
    }

    // :: error: exclusivity.postcondition.not.satisfied
    void invokeAssign(@Unique @NullTop MethodCall this) {
        @Unique Foo b;
        b = this.mthret();
    }

    void invalidate1(@Unique @NullTop MethodCall this) {
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.field.mthUnique();
        this.mthUnique();
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        this.field.mthUnique(); // invalid, refinement of field has been forgotten
    }

    void dontInvalidate(@Unique @NullTop MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthRO();
        a = this.field; // still valid, since we control all access to this
    }
}
