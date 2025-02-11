import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class LeakThis {

    @Undependable @UnknownInitialization(Object.class) @ReadOnly @NullTop LeakThis readOnly;
    @Undependable @UnknownInitialization(Object.class) @MaybeAliased LeakThis aliased;
    @Undependable @UnknownInitialization(Object.class) @Unique LeakThis unique;

    // :: error: initialization.constructor.return.type.incompatible
    @UnknownInitialization(LeakThis.class) @NullTop LeakThis() {
        this.readOnly = this;
        this.mthReadOnly();
    }

    // :: error: initialization.constructor.return.type.incompatible
    @UnknownInitialization(LeakThis.class) @NullTop LeakThis(boolean dummy) {
        this.unique = this;
        // :: error: exclusivity.type.invalidated
        this.mthUnique();
    }

    // :: error: initialization.constructor.return.type.incompatible
    @UnknownInitialization(LeakThis.class) @MaybeAliased @NullTop LeakThis(int dummy) {
        this.aliased = this;
        this.mthAliased();
    }

    void mthReadOnly(@UnknownInitialization(Object.class) @ReadOnly @NullTop LeakThis this) {
        // :: error: assignment.this-not-writable
        this.readOnly = this;
    }

    void mthAliased(@UnknownInitialization(Object.class) @MaybeAliased @NullTop LeakThis this) {
        this.aliased = this;
    }

    // :: error: exclusivity.postcondition.not.satisfied
    void mthUnique(@UnknownInitialization(Object.class) @Unique @NullTop LeakThis this) {
        this.unique = this;
    }
    
    void foo0(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) { }
    
    void bar0(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        // :: error: exclusivity.type.invalidated
        a.foo0(a);
    }
    
    void bar1(@UnknownInitialization(Object.class) @Unique LeakThis this) {
        // :: error: exclusivity.type.invalidated
        this.foo0(this);
    }
    
    void bar2(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        this.foo0(a);
    }
    
    void foo1(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) { }
    
    void bar3(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) {
        // :: error: exclusivity.type.invalidated
        a.foo1(b, b);
    }
    
    void bar4(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a) {
        // :: error: exclusivity.type.invalidated
        a.foo1(this, this);
    }
    
    void bar5(
            @UnknownInitialization(Object.class) @Unique LeakThis this,
            @UnknownInitialization(Object.class) @Unique LeakThis a,
            @UnknownInitialization(Object.class) @Unique LeakThis b) {
        this.foo1(a, b);
    }
}
