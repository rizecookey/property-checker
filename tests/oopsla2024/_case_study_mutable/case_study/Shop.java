package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class Shop {
    
    public static Shop instance = new Shop();

    @JMLClauseTranslationOnly("ensures \\result == instance;")
    @JMLClauseTranslationOnly("assignable \\nothing;")
    public static Shop getInstance() {
        return instance;
    }
    
    private @Okasaki Queue orders;

    private Shop() {
        this.orders = new Queue();
        Packing.pack(this, Shop.class);
    }

    @JMLClauseTranslationOnly("assignable this.orders;")
    public void addOrder(Shop this, Order order) {
        this.orders.insert(order);
        this.orders.toOkasaki();
    }

    public boolean processNextOrder(Shop this) {
        if (this.orders.size() > 0) {
            this.orders.removeIfPresent();
            this.orders.toOkasaki();
            return true;
        } else {
            return false;
        }
    }
}
