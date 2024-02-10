import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class BaseClass {

    public BaseClass(@Interval(min="0", max="0") int arg) {
        Packing.pack(this, BaseClass.class);
    }
}

class SubClass extends BaseClass {

    public SubClass() {
        super(0);
        Packing.pack(this, SubClass.class);
    }

    public SubClass(@Interval(min="0", max="1") int arg) {
        // :: error: argument.type.incompatible
        super(arg);
        Packing.pack(this, SubClass.class);
    }
}