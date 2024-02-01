import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class LeakThis {

    @UnknownInitialization(Object.class) @ReadOnly LeakThis readOnly;
    @UnknownInitialization(Object.class) @MaybeAliased LeakThis aliased;
    @UnknownInitialization(Object.class) @Unique LeakThis unique;

    LeakThis() {
        this.readOnly = this;
        this.mthReadOnly();
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, LeakThis.class);
    }

    LeakThis(boolean dummy) {
        // :: error: exclusivity.type.invalidated
        this.unique = this;
        // :: error: exclusivity.type.invalidated
        this.mthUnique();
    }

    // :: error: initialization.fields.uninitialized
    LeakThis(int dummy) {
        // :: error: exclusivity.type.invalidated
        this.aliased = this;
        // :: error: exclusivity.type.invalidated
        this.mthAliased();
    }

    void mthReadOnly(@UnknownInitialization(Object.class) @ReadOnly LeakThis this) {
        // :: error: assignment.this-not-writable
        this.readOnly = this;
    }

    void mthAliased(@UnknownInitialization(Object.class) @MaybeAliased LeakThis this) {
        this.aliased = this;
    }
    
    void mthUnique(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.unique = this;
    }
    
    void foo0(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) { }
    
    void bar0() {
        LeakThis a = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo0(a);
    }
    
    void bar1(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.foo0(this);
    }
    
    void bar2(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        LeakThis a = new LeakThis();
        this.foo0(a);
    }
    
    void foo1(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) { }
    
    void bar3() {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo1(b, b);
    }
    
    void bar4(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        LeakThis a = new LeakThis();
        // :: error: exclusivity.type.invalidated
        a.foo1(this, this);
    }
    
    void bar5(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        LeakThis a = new LeakThis();
        LeakThis b = new LeakThis();
        this.foo1(a, b);
    }
}
 