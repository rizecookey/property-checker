import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;

public class IntInitTest {
    
    int unannotated;
    @Remainder(remainder="0", modulus="2") int even;
    @Remainder(remainder="1", modulus="2") int odd;
    
    public IntInitTest() {
        this.helper();
        
        even = 2;
        odd = 1;
        
        // :: error: method.invocation.invalid
        this.nonHelper();

        Packing.pack(this, IntInitTest.class);
    }

    public @Remainder(remainder="0", modulus="2") int helper(@ReadOnly @UnknownInitialization IntInitTest this) {
    	// :: error: return.type.incompatible
        return this.even;
    }

    public @Remainder(remainder="0", modulus="2") int nonHelper(@ReadOnly @Initialized IntInitTest this) {
    	return this.even;
    }
}
