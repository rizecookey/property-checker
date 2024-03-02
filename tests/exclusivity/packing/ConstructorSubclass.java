import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class ConstructorSubclass extends ConstructorSuperclass {

    @Unique Object subField;

    ConstructorSubclass() {
        super();
        this.isPackedToSuperclass();
        this.subField = new Obj();
        Packing.pack(this, ConstructorSubclass.class);
    }

    ConstructorSubclass(int dummy) {
        super(dummy);
        // :: error: packing.method.invocation.invalid
        this.isPackedToSuperclass();
        this.subField = new Obj();
        Packing.pack(this, ConstructorSubclass.class);
    }

    void isPackedToSuperclass(@UnderInitialization(ConstructorSuperclass.class) @Unique @NullTop ConstructorSubclass this) {}
}
