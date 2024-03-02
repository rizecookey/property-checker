import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class ReferenceSplitting {

    void split() {
        @ReadOnly @NullTop Foo x;
        @MaybeAliased @NullTop Foo a;
        @MaybeAliased @NullTop Foo b;
        x = new Foo();      // x is refined to @Unique
        a = x;              // x is updated to @MaybeAliased
        b = x;
    }

    void split0() {
        @ReadOnly @NullTop Foo x = new Foo();
        @MaybeAliased @NullTop Foo a = x;
        @MaybeAliased @NullTop Foo b = x;
    }

    void split1() {
        @ReadOnly @NullTop Foo x;
        x = new Foo();
        @MaybeAliased @NullTop Foo a;
        a = x;
        @MaybeAliased @NullTop Foo b;
        b = x;
    }

    void refTransfer() {
        @ReadOnly @NullTop Foo x;
        @Unique @NullTop Foo a;
        @MaybeAliased @NullTop Foo b;
        @MaybeAliased @NullTop Foo c;

        x = new Foo();  // x is refined to @Unique
        a = x;          // x is updated to @ReadOnly
        x.mth();          // valid, x is not @ExclBottom
        // :: error: exclusivity.type.invalidated
        x.mthUnique();          // invalid, x is not @Unique anymore
    }
}
