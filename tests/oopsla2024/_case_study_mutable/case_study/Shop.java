package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class Shop {
    
    private @Unique @Okasaki Queue orders;

    public Shop() {
        this.orders = new Queue();
        Packing.pack(this, Shop.class);
    }

    public void addOrder(@Unique Shop this, Order order) {
        Packing.unpack(this, Shop.class);
        this.orders.insert(order);
        this.orders.toOkasaki();
        Packing.pack(this, Shop.class);
    }

    public boolean processNextOrder(@Unique Shop this) {
        if (this.orders.size() > 0) {
            Packing.unpack(this, Shop.class);
            this.orders.removeIfPresent();
            this.orders.toOkasaki();
            Packing.pack(this, Shop.class);
            return true;
        } else {
            return false;
        }
    }
}
