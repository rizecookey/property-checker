package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class Main {

    private Main() {
        Packing.pack(this, Main.class);
    }
    
    public static void main(String[] args) {
        Shop shop = new Shop();

        @AllowedFor(age="18") Product product18 = Product.product18("Louisiana Buzzsaw Carnage", 10);
        @AllowedFor(age="6") Product product6 = Product.product6("Tim & Jeffrey, All Episodes", 10);
        
        @AgedOver(age="18") Customer customer18 = Customer.customer18("Alice");
        @AgedOver(age="14") Customer customer14 = Customer.customer14("Bob");
        
        addOrder18(shop, customer18, product18);
        addOrder14(shop, customer18, product6);
        addOrder14(shop, customer14, product6);

        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();

        shop.processNextOrder();
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders;")
    public static void addOrder18(@Unique Shop shop, @AgedOver(age="18") Customer customer, @AllowedFor(age="18") Product product) {
        shop.addOrder(Order.order18(customer, product));
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders;")
    public static void addOrder14(@Unique Shop shop, @AgedOver(age="14") Customer customer, @AllowedFor(age="14") Product product) {
        shop.addOrder(Order.order14(customer, product));
    }
}
