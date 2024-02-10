import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class Constructor {

    @ReadOnly @NullTop Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    // :: error: initialization.constructor.return.type.incompatible :: error: inconsistent.constructor.type
    public Constructor() { }

    // :: error: initialization.constructor.return.type.incompatible :: error: inconsistent.constructor.type
    public @UnknownInitialization(Constructor.class) Constructor(short dummy) {
    }

    // :: error: inconsistent.constructor.type
    public @UnknownInitialization(Object.class) Constructor(long dummy) {
    }

    // :: error: inconsistent.constructor.type
    public Constructor(int dummy) {
        aliased = new Obj();
        unique = new Obj();
        Packing.pack(this, Constructor.class);
    }

    public void foo(Constructor this) {}

    public static void main() {
        new Constructor().foo();
        // not invalid because Constructor class is final
        new Constructor((short)0).foo();
        // :: error: method.invocation.invalid
        new Constructor((long)0).foo();
        new Constructor(0).foo();
    }
}

class Superclass {

    @Unique Object superField;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop Superclass() {
        this.superField = new Obj();
        Packing.pack(this, Superclass.class);
    }

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop @UnderInitialization(Object.class) Superclass(int dummy) { }
}

class Subclass extends Superclass {

    @Unique Object subField;

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop Subclass() {
        super();
        this.isPackedToSuperclass();
        this.subField = new Obj();
        Packing.pack(this, Subclass.class);
    }

    // Avoid inconsistent constructor type from LatticeSubchecker by declaring constructor as NullTop
    @NullTop Subclass(int dummy) {
        super(dummy);
        // :: error: method.invocation.invalid
        this.isPackedToSuperclass();
        this.subField = new Obj();
        Packing.pack(this, Subclass.class);
    }

    void isPackedToSuperclass(@UnderInitialization(Superclass.class) @Unique @NullTop Subclass this) {}
}