import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class A {
    
    public static final int MIN = 1, MAX = 1;

    public static void foo0(@Interval(min="2", max="2") int arg0, @Interval(min="2", max="5") int arg1) {

        // :: error: assignment.type.incompatible
        @Interval(min="MIN", max="MAX") int x = new B().field;
        
        // :: error: assignment.type.incompatible
        @Interval(min="1", max="1 + 2") int l0 = arg0;
        @Interval(min="1", max="5") int l1 = arg1;
        
        final int MAX = 5;
        // :: error: assignment.type.incompatible
        @Interval(min="1", max="MAX") int l2 = arg1;
        
        // :: error: assignment.type.incompatible
        l0 = l2;
    }
}

class B {
    
    public static final int MIN = 0, MAX = 1;

    // :: error: initialization.field.uninitialized
    public @Interval(min="MIN", max="MAX") int field;
}
