import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;

public class IntInitialized {

    @Interval(min="1", max="2") int field = 2;
}
