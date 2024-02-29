import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class AnnotatedConstructorTest {
    
    // :: error: simple.inconsistent.constructor.type
    public @B AnnotatedConstructorTest() {
        Packing.pack(this, AnnotatedConstructorTest.class);
    }

    public void foo(AnnotatedConstructorTest this, @B AnnotatedConstructorTest arg) {
        AnnotatedConstructorTest b = new AnnotatedConstructorTest();
        @B AnnotatedConstructorTest b2 = b;
        
        @A AnnotatedConstructorTest a = new AnnotatedConstructorTest();
        
        // :: error: simple.assignment.type.incompatible
        @D AnnotatedConstructorTest d = b;
    }
}
