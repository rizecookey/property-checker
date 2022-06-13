import edu.kit.iti.checker.property.subchecker.lattice.qual.*;

public final class A {

  public void foo(@NonNull A a, @Nullable A aOrNull) {
    @Nullable B bOrNull = null;
    if (aOrNull != null) {
      // :: error: assignment.type.incompatible
      bOrNull = new B();
    }
    if (bOrNull != null) {
      doSomething(a);
      // :: error: argument.type.incompatible
      doSomething(aOrNull);
    }
  }

  public static void doSomething(@NonNull A arg) {}
}
