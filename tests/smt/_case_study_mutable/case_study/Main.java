package case_study;

import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

// All type errors in this class are mended by SMT
public final class Main {

    @Pure
    private Main() {
        Packing.pack(this, Main.class);
    }
    
    public static void main(String[] args) {
        Product product18 = new Product("Louisiana Buzzsaw Carnage", 10, 18);
        Customer customer18 = new Customer("Alice", 18);
        Shop shop = new Shop();
        // :: error: agedover.argument.type.incompatible
        shop.addOrder(new Order(customer18, product18));
        Product product6 = new Product("Tim & Jeffrey, All Episodes", 10, 6);
        // :: error: agedover.argument.type.incompatible
        shop.addOrder(new Order(customer18, product6));
        Customer customer14 = new Customer("Bob", 14);

        // :: error: agedover.argument.type.incompatible
        shop.addOrder(new Order(customer14, product6));

        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();
        shop.processNextOrder();
    }
}
