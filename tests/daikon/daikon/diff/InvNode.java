package daikon.diff;

import daikon.inv.Invariant;
import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

/** Contains a pair of Invariants. Resides in the third level of the tree. Has no children. */
public class InvNode extends Node<@Nullable @MaybeAliased Invariant, @NonNullNode @NonNull @MaybeAliased Void> {

  /**
   * Either inv1 or inv2 may be null, but not both.
   *
   * @param inv1 an invariant
   * @param inv2 an invariant
   */
  @Pure
  // :: error: nullnessnode.inconsistent.constructor.type :: error: nullnessnode.contracts.postcondition.not.satisfied
  public @NonNullNode InvNode(@NonNullIfNull("inv2") @Nullable Invariant inv1, @NonNullIfNull("inv1") @Nullable Invariant inv2) {
    // :: error: nullnessnode.argument.type.incompatible
    super(inv1, inv2);
    // assert !(inv1 == null && inv2 == null) : "Both invariants may not be null";
  }

  @Pure
  @JMLClause("ensures \\result == userObject.first;")
  public @NonNullIfNull("userObject.second") @Nullable Invariant getInv1(@NonNullNode InvNode this) {
    Assert._assume("userObject.first instanceof Invariant");
    // :: error: nullnessnode.return.type.incompatible
    return (Invariant)getUserLeft();
  }

  @Pure
  @JMLClause("ensures \\result == userObject.second;")
  public @NonNullIfNull("userObject.first") @Nullable Invariant getInv2(@NonNullNode InvNode this) {
    Assert._assume("userObject.second instanceof Invariant");
    // :: error: nullnessnode.return.type.incompatible
    return (Invariant)getUserRight();
  }

  @Override
  public void accept(@NonNullNode InvNode this, Visitor v) {
    v.visit(this);
  }
}
