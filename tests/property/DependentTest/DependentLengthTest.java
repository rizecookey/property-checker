import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public class DependentLengthTest {

    public static
    @MaybeAliased
    @Length(len="a+b") List
    // :: error: length.contracts.postcondition.not.satisfied
    concat(
            int a, int b,
            @Length(len="a") List l0,
            @Length(len="b") List l1) {
        // :: error: length.return.type.incompatible :: error: nullness.return.type.incompatible
        return null;
    }

    public static void foo(
            @Length(len="1") List l0,
            @Length(len="2") List l1) {
        // :: error: length.assignment.type.incompatible
        @Length(len="3") List res = concat(1, 2, l0, l1);
    }
}
