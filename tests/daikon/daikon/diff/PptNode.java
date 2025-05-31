package daikon.diff;

import daikon.PptTopLevel;
import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.util.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

/** Contains a pair of Ppts. Resides in the second level of the tree. All its children are InvNodes. */
public class PptNode extends Node<@Nullable @MaybeAliased PptTopLevel, @NonNullNode @MaybeAliased InvNode> {

  /**
   * Either ppt1 or ppt2 may be null, but not both.
   *
   * @param ppt1 a program point
   * @param ppt2 a program point
   */
  @Pure
  // :: error: nullnessnode.inconsistent.constructor.type
  public @NonNullNode PptNode(@NonNullIfNull("ppt2") @Nullable PptTopLevel ppt1, @NonNullIfNull("ppt1") @Nullable PptTopLevel ppt2) {
    // :: error: nullnessnode.argument.type.incompatible
    super(ppt1, ppt2);
    // assert !(ppt1 == null && ppt2 == null) : "Both program points may not be null";
  }

  @Pure
  @JMLClause("ensures \\result == userObject.first;")
  public @NonNullIfNull("userObject.second") @Nullable PptTopLevel getPpt1(@NonNullNode PptNode this) {
    Assert._assume("userObject.first instanceof PptTopLevel");
    // :: error: nullnessnode.return.type.incompatible
    return (PptTopLevel) getUserLeft();
  }

  @Pure
  @JMLClause("ensures \\result == userObject.second;")
  public @NonNullIfNull("userObject.first") @Nullable PptTopLevel getPpt2(@NonNullNode PptNode this) {
    Assert._assume("userObject.second instanceof PptTopLevel");
    // :: error: nullnessnode.return.type.incompatible
    return (PptTopLevel) getUserRight();
  }

  @Override
  public void accept(@NonNullNode PptNode this, Visitor v) {
    v.visit(this);
  }
}
