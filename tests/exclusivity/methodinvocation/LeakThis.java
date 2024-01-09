import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class LeakThis {
    @ReadOnly LeakThis readOnly;
    @Unique LeakThis unique;
    @MaybeAliased LeakThis aliased;
    
    LeakThis() {
        this.readOnly = this;
        this.mthReadOnly();
    }
    
    LeakThis(boolean dummy) {
        // :: error: type.invalid
        this.unique = this;
        // :: error: type.invalid
        this.mthUnique();
    }
    
    LeakThis(int dummy) {
        // :: error: type.invalid
        this.aliased = this;
        // :: error: type.invalid
        this.mthAliased();
    }

    void mthReadOnly(@ReadOnly LeakThis this) {
        // :: error: assignment.this-not-writable
        this.readOnly = this;
    }

    void mthAliased(@MaybeAliased LeakThis this) {
        this.aliased = this;
    }
    
    void mthUnique(@Unique LeakThis this) {
        // :: error: type.invalid
        this.unique = this;
    }
    
    void foo0(@Unique LeakThis this, @Unique LeakThis a) { }
    
    void bar0() {
        LeakThis a = new LeakThis();
        // :: error: type.invalid
        a.foo0(a);
    }
    
    void bar1(@Unique LeakThis this) {
        // :: error: type.invalid
        this.foo0(this);
    }
    
    void bar2(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        this.foo0(a);
    }
    
    void foo1(@Unique LeakThis this, @Unique LeakThis a, @Unique LeakThis b) { }
    
    void bar3() {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        // :: error: type.invalid
        a.foo1(b, b);
    }
    
    void bar4(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        // :: error: type.invalid
        a.foo1(this, this);
    }
    
    void bar5(@Unique LeakThis this) {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        this.foo1(a, b);
    }
}
 