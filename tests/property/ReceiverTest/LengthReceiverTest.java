import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

import java.util.List;

public abstract class LengthReceiverTest implements List {

    public void method(
            @Length(len="1") LengthReceiverTest this,
            @Length(len="2") LengthReceiverTest that) { }

    // :: error: length.contracts.postcondition.not.satisfied
    public void foo0(
            LengthReceiverTest this,
            @Length(len="1") LengthReceiverTest a,
            @Length(len="2") LengthReceiverTest b) {
        a.method(b);

        // :: error: length.argument.type.incompatible
        a.method(a);
    }

    // :: error: length.contracts.postcondition.not.satisfied
    public void foo1(
            LengthReceiverTest this,
            @Length(len="1") LengthReceiverTest a,
            @Length(len="2") LengthReceiverTest b) {
        // :: error: length.method.invocation.invalid :: error: length.argument.type.incompatible
        b.method(a);
    }

    public void foo2(
            LengthReceiverTest this,
            @Length(len="1") LengthReceiverTest a,
            @Length(len="2") LengthReceiverTest b) {
        // :: error: length.method.invocation.invalid
        b.method(b);
    }

    // :: error: length.contracts.postcondition.not.satisfied
    public void foo3(
            LengthReceiverTest this,
            @Length(len="1") LengthReceiverTest a,
            @Length(len="2") LengthReceiverTest b) {
        // :: error: length.method.invocation.invalid :: error: length.argument.type.incompatible
        this.method(a);
    }

    public void foo4(
            LengthReceiverTest this,
            @Length(len="1") LengthReceiverTest a,
            @Length(len="2") LengthReceiverTest b) {
        // :: error: length.method.invocation.invalid
        this.method(b);
    }
}
