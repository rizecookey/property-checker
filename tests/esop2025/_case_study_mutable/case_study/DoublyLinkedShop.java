package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

@JMLClause("invariant \\invariant_for(orders);")
public final class DoublyLinkedShop {
    
    private @Unique @PossiblyEmptyDoublyLinked DoublyLinkedSortedList orders;

    @Pure
    public DoublyLinkedShop() {
        this.orders = new DoublyLinkedSortedList();
        Packing.pack(this, DoublyLinkedShop.class);
    }

    @JMLClauseTranslationOnly("assignable this.orders.footprint;")
    public void addOrder(@Unique DoublyLinkedShop this, Order order) {
        Packing.unpack(this, DoublyLinkedShop.class);
        this.orders.insert(order);
        Packing.pack(this, DoublyLinkedShop.class);
    }

    @JMLClauseTranslationOnly("assignable this.orders.footprint;")
    public boolean processNextOrder(@Unique DoublyLinkedShop this) {
        Packing.unpack(this, DoublyLinkedShop.class);
        Order result = this.orders.removeIfPresent();
        Packing.pack(this, DoublyLinkedShop.class);
        return result != null;
    }
}
