import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class MethodCall {
    @ReadOnly Foo field;

    void mthRO(@ReadOnly MethodCall this) {}

    @EnsuresUnknownInit(targetValue=Object.class)
    void mthUnique(@Unique MethodCall this) {}

    @EnsuresUnknownInit(targetValue=Object.class)
    void mthMA(@MaybeAliased MethodCall this) {}

    @EnsuresUnknownInit(targetValue=Object.class)
    void mthParam(@MaybeAliased MethodCall this, @MaybeAliased Foo arg) {}

    @Unique Foo
    mthret(@MaybeAliased MethodCall this) {
        return new Foo();
    }

    void invoke(@MaybeAliased MethodCall this) {
        @ReadOnly Foo x;
        @Unique Foo a;
        x = new Foo();   // x is refined to @Unique
        this.mthParam(x);     // x is refined to @MaybeAliased
        // :: error: exclusivity.type.invalidated
        a = x;           // invalid, x is not @Unique anymore
    }

    void invokeAssign() {
        @Unique Foo b;
        b = this.mthret();
    }

    void invalidate1(@Unique MethodCall this) {
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthUnique();
        // :: error: exclusivity.type.invalidated
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void invalidate2(@MaybeAliased MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthMA();
        // :: error: exclusivity.type.invalidated
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void dontInvalidate(@Unique MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mthRO();
        a = this.field; // still valid, since we control all access to this
    }
}
