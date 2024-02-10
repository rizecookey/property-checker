import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class IntWFTest {
    
    @Interval(min="1", max="3") int wellFormedInterval0;
    @Interval(min="1", max="1") int wellFormedInterval1;
    
    // :: error: type.invalid
    @Interval(min="1", max="0") int malFormedInterval0;
    
    // :: error: type.invalid
    @Interval(min="1", max="2") long malFormedInterval1;
    
    // :: error: type.invalid
    @Interval(min="1", max="2") String malFormedInterval2;
        
    @Remainder(remainder="1", modulus="6") int wellFormedModulus0;
    @Remainder(remainder="0", modulus="6") int wellFormedModulus1;
    @Remainder(remainder="0", modulus="1") int wellFormedModulus2;
    
    // :: error: type.invalid
    @Remainder(remainder="0", modulus="0") int malFormedModulus0;
    // :: error: type.invalid
    @Remainder(remainder="1", modulus="1") int malFormedModulus1;
    // :: error: type.invalid
    @Remainder(remainder="2", modulus="1") int malFormedModulus2;
    // :: error: type.invalid
    @Remainder(remainder="2", modulus="2") int malFormedModulus3;
    // :: error: type.invalid
    @Remainder(remainder="3", modulus="2") int malFormedModulus4;

    public IntWFTest() {
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, IntWFTest.class);
    }
}
