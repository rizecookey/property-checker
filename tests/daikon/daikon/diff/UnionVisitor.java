package daikon.diff;

import daikon.PptTopLevel;
import daikon.inv.Invariant;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.RequiresNonNull;

import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** Computes A union B, where A and B are the two sets of invariants. */
public class UnionVisitor extends DepthFirstVisitor {

  private InvMap result = new InvMap();
  private @MonotonicNonNull PptTopLevel currentPpt;

  public InvMap getResult() {
    return result;
  }

  /** Every node has at least one non-null ppt. Add one of the non-null ppt to the result. */
  @Override
  public void visit(@NonNullNode PptNode node) {
    PptTopLevel ppt1 = node.getPpt1();
    PptTopLevel ppt2 = node.getPpt2();
    //@SuppressWarnings("nullness") // application invariant: at least one of ppt1 and ppt2 is non-null
    // :: error: nullness.assignment.type.incompatible
    @Unique @NonNull PptTopLevel pptNonNull = (ppt1 != null ? ppt1 : ppt2);
    result.addPpt(pptNonNull);
    currentPpt = pptNonNull;
    super.visit(node);
  }

  /**
   * If only one invariant is non-null, always add it. If two invariants are non-null, add the
   * invariant with the better (higher) confidence.
   */
  @Override
  /*@SuppressWarnings(
      "nullness:contracts.precondition.override" // visitor invariant, because the PptNode has
  // already been visited
  )*/
  @RequiresNonNull("currentPpt")
  // visitor invariant
  // Ill-typed and thus unprovable: A client calling this method from a superclass may violate this precondition
  // :: error: nullness.contracts.precondition.override.invalid
  public void visit(@NonNullNode InvNode node) {
    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();
    if (inv1 == null) {
      //assert inv2 != null : "@AssumeAssertion(nullness): at least one of inv1 and inv2 is non-null";
      // :: error: nullness.argument.type.incompatible
      result.add(currentPpt, inv2);
    } else if (inv2 == null) {
      result.add(currentPpt, inv1);
    } else {
      if (inv1.getConfidence() >= inv2.getConfidence()) {
        result.add(currentPpt, inv1);
      } else {
        result.add(currentPpt, inv2);
      }
    }
  }
}
