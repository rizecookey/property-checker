import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Constructor {

    @ReadOnly Object readOnly;
    @MaybeAliased Object aliased;
    @Unique Object unique;

    public Constructor() {

    }

    public @UnknownInitialization(Object.class) Constructor(boolean dummy) {
    }

    public Constructor(int dummy) {
        unique = new Object();
        Packing.pack(this, Constructor.class);
    }

    public void foo() {}

    public static void main() {
        new Constructor().foo();
        new Constructor(false).foo();
        new Constructor(0).foo();
    }
}