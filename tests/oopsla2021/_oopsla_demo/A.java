import edu.kit.kastel.property.subchecker.lattice.qual.*;
import org.checkerframework.checker.nullness.qual.*;

public final class A {

  public void foo(@NonNull A a, @Nullable A aOrNull) {
    @Nullable B bOrNull = null;
    if (aOrNull != null) {
      bOrNull = new B();
    }
    if (bOrNull != null) {
      doSomething(a);
      doSomething(aOrNull);
    }
  }

  public static void doSomething(@NonNull A arg) {}
}
