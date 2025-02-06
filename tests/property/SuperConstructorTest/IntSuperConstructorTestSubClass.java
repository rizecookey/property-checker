import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class IntSuperConstructorTestSubClass extends IntSuperConstructorTestBaseClass {

    public IntSuperConstructorTestSubClass() {
        super(0);
    }

    public IntSuperConstructorTestSubClass(@Interval(min="0", max="1") int arg) {
        // :: error: interval.argument.type.incompatible
        super(arg);
    }
}
