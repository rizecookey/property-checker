import java.util.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;

public class IntTest {
    
    // :: error: interval.assignment.type.incompatible
    @Interval(min="1", max="2") int field = 3;
    
    public static void foo0(@Interval(min="2", max="2") int arg0, @Interval(min="2", max="5") int arg1) {
        @Interval(min="1", max="3") int l0 = arg0;
        @Interval(min="1", max="5") int l1 = arg1;
        
        // :: error: interval.assignment.type.incompatible
        @Interval(min="1", max="2") int l2 = arg1;

        // can be verified using SMT
        // :: error: interval.assignment.type.incompatible
        @Interval(min="4", max="7") int l3 = arg0 + arg1;
        
        // :: error: interval.assignment.type.incompatible
        @Interval(min="2", max="5") int l4 = arg0 + arg1;
        // :: error: interval.assignment.type.incompatible
        @Interval(min="2", max="2") int l5 = arg0 + arg1;
        
        @Interval(min="4", max="7") @Remainder(remainder="1", modulus="4") int lit0 = 5;
        
        // :: error: remainder.assignment.type.incompatible
        lit0 = 6;
        
        @Interval(min="4", max="7") int lit1 = 5;
        
        // :: error: interval.unary.increment.type.incompatible
        ++lit1;
    }
    
    public static void foo1(
            @Remainder(remainder="1", modulus="6") int arg0,
            @Remainder(remainder="4", modulus="6") int arg1) {
        @Remainder(remainder="1", modulus="3") int a = arg0;
        a = arg1;
    }
    
    public static void foo2(@Remainder(remainder="1", modulus="6") @Interval(min="1", max="5") int arg0) {
        foo1(arg0, 4);
        
        // :: error: remainder.argument.type.incompatible
        foo1(arg0, 0);
        
        // :: error: remainder.assignment.type.incompatible
        @Remainder(remainder="1", modulus="12") @Interval(min="1", max="5") int a = arg0;

        // :: error: interval.assignment.type.incompatible
        @Remainder(remainder="1", modulus="6") @Interval(min="3", max="3") int b = arg0;

        // :: error: interval.assignment.type.incompatible :: error: remainder.assignment.type.incompatible
        @Remainder(remainder="1", modulus="12") @Interval(min="3", max="3") int c = arg0;
        
        @Remainder(remainder="1", modulus="6") @Interval(min="1", max="5") int d = arg0;
    }
}
