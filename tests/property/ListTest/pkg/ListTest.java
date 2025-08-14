package pkg;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;


class ListTest {

    void foo() {
        @Interval(min="1",max="2") int i = 2;
        @Length(len="1") List a = new List("foo");
        @Length(len="2") List b = new List("bar", new List("baz"));
        Object el = a.prependAll(b).nth(i);
    }
}