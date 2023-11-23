import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Primitives {
    @ExclMut Foo excl;
    @ShrMut Foo shr;
    @Immutable Foo immut;
    
    boolean b;
    @Immutable boolean immutB;
    @ReadOnly boolean readOnlyB;
    // :: error: type.invalid.annotations.on.use
    @ShrMut boolean shrMutB;
    // :: error: type.invalid.annotations.on.use
    @ExclMut boolean exclMutB;
    
    int i;
    @Immutable int immutI;
    @ReadOnly int readOnlyI;
    // :: error: type.invalid.annotations.on.use
    @ShrMut int shrMutI;
    // :: error: type.invalid.annotations.on.use
    @ExclMut int exclMutI;
    
    String s;
    @Immutable String immutS;
    @ReadOnly String readOnlyS;
    // :: error: type.invalid.annotations.on.use
    @ShrMut String shrMutS;
    // :: error: type.invalid.annotations.on.use
    @ExclMut String exclMutS;

    void assignWritableThisObjectField0(@ExclMut Primitives this) {
        this.excl = new Foo();
        this.shr = new Foo();
        this.immut = new Foo();
    }

    void assignWritableThisPrimitiveField0(@ExclMut Primitives this, int x, boolean b) {
        this.i = 42;
        this.i = 10 * 4 + 2;
        this.i = - (10 * 4 + 2);
        this.i = 10 * x;
        this.i = - x;
        
        this.b = true;
        this.b = true && false;
        this.b = !true;
        this.b = false || b;
    }

    void assignWritableThisObjectField1(@ShrMut Primitives this) {
        this.excl = new Foo();
        this.shr = new Foo();
        this.immut = new Foo();
    }

    void assignWritableThisPrimitiveField1(@ShrMut Primitives this, int x, boolean b) {
        this.i = 42;
        this.i = 10 * 4 + 2;
        this.i = - (10 * 4 + 2);
        this.i = 10 * x;
        this.i = - x;
        
        this.b = true;
        this.b = true && false;
        this.b = !true;
        this.b = false || b;
    }

    void assignWritableThisStringField0(@ExclMut Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    void assignWritableThisStringField1(@ShrMut Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    void assignNonWritableThis(@Immutable Primitives this) {
        // :: error: assignment.this-not-writable
        this.excl = new Foo();
        // :: error: assignment.this-not-writable
        this.shr = new Foo();
        // :: error: assignment.this-not-writable
        this.immut = new Foo();
        // :: error: assignment.this-not-writable
        this.i = 42;
        // :: error: assignment.this-not-writable
        this.s = "42";
    }

    @ExclMut Foo copyExclFieldReference() {
        // :: error: type.invalid
        return this.excl;
    }

    @ShrMut Foo copyShrFieldReference() {
        return this.shr;
    }

    @Immutable Foo copyImmutFieldReference() {
        return this.immut;
    }

    int copyPrimitiveField() {
        return this.i;
    }
}
