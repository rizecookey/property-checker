import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Primitives {
    @Unique Foo excl;
    @MaybeAliased Foo shr;
    @MaybeAliased Foo immut;
    
    boolean b;
    @MaybeAliased boolean immutB;
    @ReadOnly boolean readOnlyB;
    // :: error: type.invalid.annotations.on.use
    @MaybeAliased boolean shrMutB;
    // :: error: type.invalid.annotations.on.use
    @Unique boolean exclMutB;
    
    int i;
    @MaybeAliased int immutI;
    @ReadOnly int readOnlyI;
    // :: error: type.invalid.annotations.on.use
    @MaybeAliased int shrMutI;
    // :: error: type.invalid.annotations.on.use
    @Unique int exclMutI;
    
    String s;
    @MaybeAliased String immutS;
    @ReadOnly String readOnlyS;
    // :: error: type.invalid.annotations.on.use
    @MaybeAliased String shrMutS;
    // :: error: type.invalid.annotations.on.use
    @Unique String exclMutS;

    void assignWritableThisObjectField0(@Unique Primitives this) {
        this.excl = new Foo();
        this.shr = new Foo();
        this.immut = new Foo();
    }

    void assignWritableThisPrimitiveField0(@Unique Primitives this, int x, boolean b) {
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

    void assignWritableThisObjectField1(@MaybeAliased Primitives this) {
        this.excl = new Foo();
        this.shr = new Foo();
        this.immut = new Foo();
    }

    void assignWritableThisPrimitiveField1(@MaybeAliased Primitives this, int x, boolean b) {
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

    void assignWritableThisStringField0(@MaybeAliased Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    void assignWritableThisStringField1(@MaybeAliased Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    void assignNonWritableThis(@MaybeAliased Primitives this) {
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

    @Unique Foo copyExclFieldReference() {
        // :: error: type.invalid
        return this.excl;
    }

    @MaybeAliased Foo copyShrFieldReference() {
        return this.shr;
    }

    @MaybeAliased Foo copyImmutFieldReference() {
        return this.immut;
    }

    int copyPrimitiveField() {
        return this.i;
    }
}
