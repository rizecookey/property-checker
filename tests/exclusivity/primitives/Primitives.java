import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

@SuppressWarnings({"initialization","lattice"})
public class Primitives {
    Foo foo;
    @Unique Foo unique;
    @MaybeAliased Foo aliased;
    @ReadOnly Foo readOnly;
    
    boolean b;
    
    int i;
    
    String s;

    void assignUniqueThisObjectField(@Unique Primitives this) {
        this.unique = new Foo();
        this.aliased = new Foo();
        this.readOnly = new Foo();
    }

    void assignAliasedThisObjectField(@MaybeAliased Primitives this) {
        this.unique = new Foo();
        this.aliased = new Foo();
        this.readOnly = new Foo();
    }

    void assignUniqueThisPrimitiveField(@Unique Primitives this, int x, boolean b) {
        this.i = 42;
        this.i = 10 * 4 + 2;
        this.i = - (10 * 4 + 2);
        this.i = 10 * x;
        this.i = - x;
        
        this.b = true;
        this.b = true && false;
        this.b = !true;
        this.b = false || b;
        this.i = 42;
        this.i = 10 * 4 + 2;
        this.i = - (10 * 4 + 2);
        this.i = 10 * x;
        this.i = - x;
    }

    void assignAliasedThisPrimitiveField(@MaybeAliased Primitives this, int x, boolean b) {
        this.i = 42;
        this.i = 10 * 4 + 2;
        this.i = - (10 * 4 + 2);
        this.i = 10 * x;
        this.i = - x;
        
        this.b = true;
        this.b = true && false;
        this.b = !true;
        this.b = false || b;
    }

    void assignUniqueThisStringField(@Unique Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    void assignAliasedThisStringField(@MaybeAliased Primitives this, String s) {
        this.s = "42";
        this.s = "4" + "2";
        this.s = "4" + s;
    }

    @Unique Foo copyUniqueFieldReference() {
        // :: error: exclusivity.type.invalidated
        return this.unique;
    }

    @MaybeAliased Foo copyAliasedFieldReference() {
        return this.aliased;
    }

    int copyPrimitiveField() {
        return this.i;
    }
}
