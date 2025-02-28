import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

class ReferenceSplitting {

    void split() {
        @ReadOnly @Nullable Foo x;
        @MaybeAliased @Nullable Foo a;
        @MaybeAliased @Nullable Foo b;
        x = new Foo();      // x is refined to @Unique
        a = x;              // x is updated to @MaybeAliased
        b = x;
    }

    void split0() {
        @ReadOnly @Nullable Foo x = new Foo();
        @MaybeAliased @Nullable Foo a = x;
        @MaybeAliased @Nullable Foo b = x;
    }

    void split1() {
        @ReadOnly @Nullable Foo x;
        x = new Foo();
        @MaybeAliased @Nullable Foo a;
        a = x;
        @MaybeAliased @Nullable Foo b;
        b = x;
    }

    void refTransfer() {
        @ReadOnly @Nullable Foo x;
        @Unique @Nullable Foo a;
        @MaybeAliased @Nullable Foo b;
        @MaybeAliased @Nullable Foo c;

        x = new Foo();  // x is refined to @Unique
        a = x;          // x is updated to @ReadOnly
        x.mth();          // valid, x is not @ExclBottom
        // :: error: exclusivity.type.invalidated :: error: packing.method.invocation.invalid
        x.mthUnique();          // invalid, x is not @Unique anymore
    }
}
