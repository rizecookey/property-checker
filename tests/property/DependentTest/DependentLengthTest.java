import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public class DependentLengthTest {

    public static
    @JMLClause("requires a+c > 0 && b+d > 0")
    @MaybeAliased
    @Length(min="a+c", max="b+d") List
    // :: error: contracts.postcondition.not.satisfied
    concat(
            int a, int b, int c, int d,
            @Length(min="a", max="b") List l0,
            @Length(min="c", max="d") List l1) {
        // :: error: return.type.incompatible
        return null;
    }

    public static void foo(
            @Length(min="1", max="1") List l0,
            @Length(min="2", max="2") List l1) {
        // :: error: assignment.type.incompatible :: error: argument.type.incompatible
        @Length(min="3", max="3") List res = concat(1, 1, 2, 2, l0, l1);
    }
}
