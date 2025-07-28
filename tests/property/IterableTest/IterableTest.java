import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

import java.util.ArrayList;
import java.util.List;

public class IterableTest {

    private List<@NonNull Object> list = new ArrayList<>();
    private @NonNull Object @NonNull [] arr = new Object[0];

    public void iterateList() {
        for (Object obj : list) {
            obj.toString();
        }
    }

    public void iterateArr() {
        for (Object obj : arr) {
            obj.toString();
        }
    }

    public void iterateListOther(IterableTest other) {
        for (Object obj : other.list) {
            obj.toString();
        }
    }

    public void iterateArrOther(IterableTest other) {
        for (Object obj : other.arr) {
            obj.toString();
        }
    }
}
