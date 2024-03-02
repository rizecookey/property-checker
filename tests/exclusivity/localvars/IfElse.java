import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public class IfElse {

    void ifElse0(@Unique IfElse this, @Unique IfElse other, boolean b) {
        other.isUnique();

        @Unique IfElse local = null;
        if (b) {
            local = other;
        } else {
            other.isUnique();
        }

        // :: error: exclusivity.type.invalidated
        other.isUnique();
    }

    void ifElse1(@Unique IfElse this, @Unique IfElse other, boolean b) {
        other.isUnique();

        @MaybeAliased IfElse local = null;
        if (b) {
            local = other;
        } else {
            other.isUnique();
        }

        // :: error: exclusivity.type.invalidated
        other.isUnique();
    }

    void ifElse2(@Unique IfElse this, @Unique IfElse other, boolean b) {
        other.isUnique();

        @ReadOnly IfElse local = null;
        if (b) {
            local = other;
        } else {
            other.isUnique();
        }

        other.isUnique();
    }

    void isUnique(@Unique IfElse this) {}
}
