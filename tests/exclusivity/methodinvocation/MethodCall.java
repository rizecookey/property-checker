import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class MethodCall {

    @ReadOnly @NullTop Foo field;

    @NullTop MethodCall() {
        Packing.pack(this, MethodCall.class);
    }

    void mthRO(@UnknownInitialization @ReadOnly @NullTop MethodCall this) {}

    void mthUnique(@UnknownInitialization @Unique MethodCall this) {}

    void mthMA(@UnknownInitialization @MaybeAliased MethodCall this) {}

    void mthParam(@UnknownInitialization @MaybeAliased MethodCall this, @UnknownInitialization @MaybeAliased Foo arg) {}

    @Unique Foo mthret(@MaybeAliased MethodCall this) {
        return new Foo();
    }

    @EnsuresUnknownInit(targetValue=Object.class)
    void invoke(@MaybeAliased MethodCall this) {
        @ReadOnly Foo x;
        @Unique Foo a;
        x = new Foo();   // x is refined to @Unique
        this.mthParam(x);     // x is refined to @MaybeAliased
        // :: error: exclusivity.type.invalidated
        a = x;           // invalid, x is not @Unique anymore
    }

    // :: error: exclusivity.postcondition.not.satisfied
    void invokeAssign(@Unique MethodCall this) {
        @Unique Foo b;
        b = this.mthret();
    }

    void invalidate1(@Unique MethodCall this) {
        Packing.unpack(this, MethodCall.class);
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthUnique();
        // :: error: exclusivity.type.invalidated
        a = this.field; // invalid, refinement of field has been forgotten
        Packing.pack(this, MethodCall.class);
    }

    void dontInvalidate(@Unique MethodCall this) {
        Packing.unpack(this, MethodCall.class);
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthRO();
        a = this.field; // still valid, since we control all access to this
        Packing.pack(this, MethodCall.class);
    }
}
