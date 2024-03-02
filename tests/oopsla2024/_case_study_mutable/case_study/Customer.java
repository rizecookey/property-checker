package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public final class Customer {
    
    public final String name;
    public final @Interval(min="14", max="150") int age;

    @JMLClause("ensures this.name == name && this.age == age;")
    @JMLClause("assignable \\nothing;")
    // :: error: agedover.inconsistent.constructor.type
    public @AgedOver(age="age") Customer(String name, @Interval(min="14", max="150") int age) {
        this.name = name;
        this.age = age;
        Packing.pack(this, Customer.class);
    }

    @JMLClause("ensures \\result.name == name && \\result.age == 18;")
    @JMLClause("assignable \\nothing;")
    public static @AgedOver(age="18") Customer customer18(String name) {
        // :: error: agedover.return.type.incompatible
        return new Customer(name, 18);
    }

    @JMLClause("ensures \\result.name == name && \\result.age == 14;")
    @JMLClause("assignable \\nothing;")
    public static @AgedOver(age="14") Customer customer14(String name) {
        // :: error: agedover.return.type.incompatible
        return new Customer(name, 14);
    }
}
