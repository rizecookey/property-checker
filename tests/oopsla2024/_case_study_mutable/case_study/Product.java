package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class Product {
    
    public final String title;
    public final @Interval(min="0", max="2147483647") int price;
    public final @Interval(min="0", max="18") int ageRestriction;

    @JMLClause("ensures this.title == title && this.price == price && this.ageRestriction == ageRestriction;")
    @JMLClause("assignable \\nothing;")
    // :: error: allowedfor.inconsistent.constructor.type
    public @AllowedFor(age="ageRestriction") Product(
            String title,
            @Interval(min="0", max="2147483647") int price,
            @Interval(min="0", max="18") int ageRestriction) {
        this.title = title;
        this.price = price;
        this.ageRestriction = ageRestriction;
        Packing.pack(this, Product.class);
    }

    @JMLClause("ensures \\result.title == title && \\result.price == price && \\result.ageRestriction == 18;")
    @JMLClause("assignable \\nothing;")
    public static @AllowedFor(age="18") Product product18(
            String title,
            @Interval(min="0", max="2147483647") int price) {
        // :: error: allowedfor.return.type.incompatible
        return new Product(title, price, 18);
    }

    @JMLClause("ensures \\result.title == title && \\result.price == price && \\result.ageRestriction == 6;")
    @JMLClause("assignable \\nothing;")
    public static @AllowedFor(age="6") Product product6(
            String title,
            @Interval(min="0", max="2147483647") int price) {
        // :: error: allowedfor.return.type.incompatible
        return new Product(title, price, 6);
    }
}
