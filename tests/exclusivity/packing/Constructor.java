import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

final class Constructor {

    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    // :: error: initialization.constructor.return.type.incompatible
    public Constructor() { }

    // :: error: initialization.constructor.return.type.incompatible
    public @UnknownInitialization(Constructor.class) Constructor(short dummy) {
    }

    public @UnknownInitialization(Object.class) Constructor(long dummy) {
    }

    public Constructor(int dummy) {
        unique = new Object();
        Packing.pack(this, Constructor.class);
    }

    public void foo() {}

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

    Superclass() {
        this.superField = new Object();
        Packing.pack(this, Superclass.class);
    }

    @UnderInitialization(Object.class) Superclass(int dummy) { }
}

class Subclass extends Superclass {

    @Unique Object subField;

    Subclass() {
        super();
        this.isPackedToSuperclass();
        this.subField = new Object();
        Packing.pack(this, Subclass.class);
    }

    Subclass(int dummy) {
        super(dummy);
        // :: error: method.invocation.invalid
        this.isPackedToSuperclass();
        this.subField = new Object();
        Packing.pack(this, Subclass.class);
    }

    void isPackedToSuperclass(@UnderInitialization(Superclass.class) @Unique Subclass this) {}
}