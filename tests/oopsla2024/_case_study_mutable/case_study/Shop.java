package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Shop {
    
    private @Unique @PossiblyEmpty SortedList orders;

    @Pure
    public Shop() {
        this.orders = new SortedList();
        Packing.pack(this, Shop.class);
    }

    @JMLClauseTranslationOnly("assignable this.orders.*, \\infinite_union(Node n; n.*);")
    public void addOrder(@Unique Shop this, Order order) {
        Packing.unpack(this, Shop.class);
        this.orders.insert(order);
        Packing.pack(this, Shop.class);
    }

    @JMLClauseTranslationOnly("assignable this.orders.*, this.orders.first.packed, \\infinite_union(Node n; n.*);")
    public boolean processNextOrder(@Unique Shop this) {
        Packing.unpack(this, Shop.class);
        Order result = this.orders.removeIfPresent();
        Packing.pack(this, Shop.class);
        return result != null;
    }
}
