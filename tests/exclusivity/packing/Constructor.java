import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Constructor {

    @ReadOnly @NullTop Object readOnly;
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
        aliased = new Obj();
        unique = new Obj();
        Packing.pack(this, Constructor.class);
    }

    public void foo(Constructor this) {}

    public static void main() {
        new Constructor().foo();
        // not invalid because Constructor class is final
        new Constructor((short)0).foo();
        // :: error: packing.method.invocation.invalid
        new Constructor((long)0).foo();
        new Constructor(0).foo();
    }
}
