import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class MethodCall {
    @ReadOnly Foo field;

    void mth(@ReadOnly MethodCall this) {}

    void mthParam(@ShrMut MethodCall this, @ShrMut Foo arg) {}

    @ExclMut Foo
    mthret(@ShrMut MethodCall this) {
        return new Foo();
    }

    void invoke(@ShrMut MethodCall this) {
        @ReadOnly Foo x;
        @ExclMut Foo a;
        x = new Foo();   // x is refined to @ExclMut
        this.mthParam(x);     // x is refined to @ShrMut
        // :: error: type.invalid
        a = x;           // invalid, x is not @ExclMut anymore
    }

    void invokeAssign() {
        @ExclMut Foo b;
        b = this.mthret();
    }

    void invalidate1(@ExclMut MethodCall this) {
        @ExclMut Foo a;
        this.field = new Foo(); // field is refined to @ExclMut
        this.mth();
        // :: error: type.invalid
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void invalidate2(@ShrMut MethodCall this) {
        @ExclMut Foo recv = new Foo();
        @ExclMut Foo a;
        this.field = new Foo(); // field is refined to @ExclMut
        recv.mth();
        // :: error: type.invalid
        a = this.field; // invalid, refinement of field has been forgotten
    }

    void dontInvalidate(@ExclMut MethodCall this) {
        @ExclMut Foo recv = new Foo();
        @ExclMut Foo a;
        this.field = new Foo(); // field is refined to @ExclMut
        recv.mth();
        a = this.field; // still valid, since we control all access to this
    }
}
