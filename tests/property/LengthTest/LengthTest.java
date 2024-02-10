import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public abstract class LengthTest {

    public static void foo0(
            @Length(min="2", max="2") List arg0,
            @Length(min="2", max="5") List arg1) {
        @Length(min="1", max="3") List l0 = arg0;
        @Length(min="1", max="5") List l1 = arg1;

        // :: error: assignment.type.incompatible
        @Length(min="3", max="5") List l2 = arg1;
    }

    public static void foo1(
            @Length(min="2", max="2") List arg0,
            @Length(min="2", max="5") List arg1) {
        List l0 = arg0;
        @Length(min="2", max="2") List l1 = l0;

        foo0(arg0, arg1);

        // :: error: argument.type.incompatible
        bar(arg0, arg1, true);

        @Length(min="2", max="3") List l2 = bar(arg0, arg1, true);

        // :: error: assignment.type.incompatible
        @Length(min="2", max="2") List l3 = bar(arg0, arg1, true);
    }

    public static @Length(min="2", max="3") List bar(
            @Length(min="2", max="2") List arg0,
            @Length(min="3", max="3") List arg1,
            boolean b) {
        return b ? arg0 : arg1;
    }

    public static @Length(min="2", max="3") List baz0(
            @Length(min="2", max="2") List arg0,
            @Length(min="3", max="3") List arg1,
            boolean b) {
        if (b) {
            return arg0;
        } else {
            return arg1;
        }
    }

    public static @Length(min="2", max="3") List baz1(
            @Length(min="2", max="2") List arg0,
            @Length(min="3", max="3") List arg1,
            boolean b) {
        List result;
        if (b) {
            result = arg0;
        } else {
            result = arg1;
        }
        return result;
    }

    public static void foo2(
            @Length(min="2", max="2") List arg0,
            @Length(min="3", max="3") List arg1,
            boolean b) {
       List l0 = b ? arg0 : arg1;
       @Length(min="2", max="3") List l1 = l0;
    }

    public abstract @Length(min="2", max="3") List override0(
            LengthTest this,
            @Length(min="2", max="3") List a);

    public abstract @Length(min="2", max="3") List override1(LengthTest this);

    public void override2(
            LengthTest this,
            @Length(min="2", max="3") List a) { }
}

abstract class SubLengthTest extends LengthTest {

    public abstract @Length(min="2", max="2") List override0(
            SubLengthTest this,
            @Length(min="1", max="4") List a);

    // :: error: override.return.invalid
    public abstract @Length(min="2", max="6") List override1(SubLengthTest this);

    public void override2(
            SubLengthTest this,
            // :: error: override.param.invalid
            @Length(min="1", max="1") List a) { }
}
