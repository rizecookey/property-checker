import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class LeakThis {
    @ReadOnly LeakThis readOnly;
    @ExclMut LeakThis exclMut;
    @ShrMut LeakThis shrMut;
    @Immutable LeakThis immut;
    
    LeakThis() {
        this.readOnly = this;
        this.mth0();
    }
    
    LeakThis(boolean dummy) {
        // :: error: type.invalid
        this.exclMut = this;
        // :: error: type.invalid
        this.mth3();
    }
    
    LeakThis(int dummy) {
        // :: error: type.invalid
        this.shrMut = this;
        // :: error: type.invalid
        this.mth1();
    }
    
    LeakThis(short dummy) {
        // :: error: type.invalid
        this.immut = this;
        // :: error: type.invalid
        this.mth2();
    }

    void mth0(@ReadOnly LeakThis this) {
        // :: error: assignment.this-not-writable
        this.readOnly = this;
    }

    void mth1(@ShrMut LeakThis this) {
        this.shrMut = this;
    }
    
    void mth2(@Immutable LeakThis this) {
        // :: error: assignment.this-not-writable
        this.immut = this;
    }
    
    void mth3(@ExclMut LeakThis this) {
        // :: error: type.invalid
        this.exclMut = this;
    }
    
    void foo0(@ExclMut LeakThis this, @ExclMut LeakThis a) { }
    
    void bar0() {
        LeakThis a = new LeakThis();
        // :: error: type.invalid
        a.foo0(a);
    }
    
    void bar1(@ExclMut LeakThis this) {
        // :: error: type.invalid
        this.foo0(this);
    }
    
    void bar2(@ExclMut LeakThis this) {
        LeakThis a = new LeakThis();
        this.foo0(a);
    }
    
    void foo1(@ExclMut LeakThis this, @ExclMut LeakThis a, @ExclMut LeakThis b) { }
    
    void bar3() {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        // :: error: type.invalid
        a.foo1(b, b);
    }
    
    void bar4(@ExclMut LeakThis this) {
        LeakThis a = new LeakThis();
        // :: error: type.invalid
        a.foo1(this, this);
    }
    
    void bar5(@ExclMut LeakThis this) {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        this.foo1(a, b);
    }
}
 