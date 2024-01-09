import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class MethodCall {
    @ReadOnly Foo field;

    void mth(@ReadOnly MethodCall this) {}

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
        // :: error: type.invalid
        a = x;           // invalid, x is not @Unique anymore
    }

    void invokeAssign() {
        @Unique Foo b;
        b = this.mthret();
    }

    void invalidate1(@Unique MethodCall this) {
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        this.mth();
        // :: error: type.invalid
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void invalidate2(@MaybeAliased MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        recv.mth();
        // :: error: type.invalid
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void dontInvalidate(@Unique MethodCall this) {
        @Unique Foo recv = new Foo();
        @Unique Foo a;
        this.field = new Foo(); // field is refined to @Unique
        recv.mth();
        a = this.field; // still valid, since we control all access to this
    }
}
