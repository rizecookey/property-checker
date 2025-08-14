import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import edu.kit.kastel.property.checker.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class PreservingUpdateDependentTest {

    // :: error: interval.assignment.type.incompatible
    @Dependable @Interval(min="1", max="this.intField1") int intField0 = 1;
    @Dependable @Interval(min="1", max="2") int intField1 = 1;
    @NonNull Object objField = new Object();

    @NonMonotonic
    void nonPreservingAliased0(@MaybeAliased PreservingUpdateDependentTest this) {
        // :: error: initialization.write.committed.dependable.field
        this.intField0 = 0;
    }

    @NonMonotonic
    void nonPreservingAliased1(@MaybeAliased PreservingUpdateDependentTest this, @MaybeAliased PreservingUpdateDependentTest other) {
        other.objField = new Object();
        // :: error: initialization.write.committed.dependable.field
        this.intField1 = 0;
    }
}
