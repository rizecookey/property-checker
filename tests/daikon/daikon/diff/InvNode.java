package daikon.diff;

import daikon.inv.Invariant;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** Contains a pair of Invariants. Resides in the third level of the tree. Has no children. */
public class InvNode extends Node<@Nullable Invariant, @NonNullNode @NonNull Void> {

  /**
   * Either inv1 or inv2 may be null, but not both.
   *
   * @param inv1 an invariant
   * @param inv2 an invariant
   */
  public @NonNullNode InvNode(@NonNullIfNull("inv2") @Nullable Invariant inv1, @NonNullIfNull("inv1") @Nullable Invariant inv2) {
    super(inv1, inv2);
    assert !(inv1 == null && inv2 == null) : "Both invariants may not be null";
  }

  @Pure
  @JMLClause("ensures \\result == userObject.first")
  public @NonNullIfNull("userObject.second") @Nullable Invariant getInv1(@NonNullNode InvNode this) {
    return getUserLeft();
  }

  @Pure
  @JMLClause("ensures \\result == userObject.second")
  public @NonNullIfNull("userObject.first") @Nullable Invariant getInv2(@NonNullNode InvNode this) {
    return getUserRight();
  }

  @Override
  public void accept(Visitor v) {
    v.visit(this);
  }
}
