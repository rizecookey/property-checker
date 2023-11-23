import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

class Foo {

    public void mth(@ReadOnly Foo this) {}
}
