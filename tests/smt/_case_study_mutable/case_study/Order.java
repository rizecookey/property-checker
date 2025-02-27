package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Order {

    public final @AgedOver(age="product.ageRestriction") Customer customer;
    public final Product product;

    @JMLClause("ensures this.customer == customer && this.product == product;")
    @JMLClause("assignable \\nothing;") @Pure
    // :: error: agedover.contracts.postcondition.not.satisfied
    public Order(@AgedOver(age="product.ageRestriction") Customer customer, Product product) {
        this.customer = customer;
        this.product = product;
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, Order.class);
    }

    @JMLClause("ensures \\result == this.product.price;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getPrice(@MaybeAliased Order this) {
        return product.getPrice();
    }
}
