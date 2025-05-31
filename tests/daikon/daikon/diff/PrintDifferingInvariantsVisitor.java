package daikon.diff;

import daikon.inv.Invariant;
import java.io.PrintStream;
import java.util.logging.Level;
import java.util.logging.Logger;
import org.checkerframework.checker.nullness.qual.Nullable;

import org.checkerframework.dataflow.qual.Pure;
import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** Prints the differing invariant pairs. */
public class PrintDifferingInvariantsVisitor extends PrintAllVisitor {

  /** Logger for debugging information. */
  public static final Logger debug = Logger.getLogger("daikon.diff.DetailedStatisticsVisitor");

  /** Create an instance of PrintDifferingInvariantsVisitor. */
  public PrintDifferingInvariantsVisitor(PrintStream ps, boolean verbose, boolean printEmptyPpts) {
    super(ps, verbose, printEmptyPpts);
  }

  @Override
  public void visit(@NonNullNode InvNode node) {
    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();
    // :: error: nullnessnode.argument.type.incompatible
    if (shouldPrint(inv1, inv2)) {
      super.visit(node);
    }
  }

  /**
   * Returns true if the pair of invariants should be printed, depending on their type,
   * relationship, and printability.
   */
  @JMLClause("requires_free debug != null && Level.FINE != null;")
  // :: error: nullnessnode.contracts.postcondition.not.satisfied
  protected boolean shouldPrint(@NonNullIfNull("inv2") @Nullable Invariant inv1, @NonNullIfNull("inv1") @Nullable Invariant inv2) {
    // :: error: nullnessnode.argument.type.incompatible
    int rel = DetailedStatisticsVisitor.determineRelationship(inv1, inv2);
    if (!shouldPrintBasedOnRel(rel)) {
      if (debug.isLoggable(Level.FINE)) {
        debug.fine(" Returning false");
      }

      return false;
    }

    if ((inv1 == null || !inv1.isWorthPrinting()) && (inv2 == null || !inv2.isWorthPrinting())) {
      if (debug.isLoggable(Level.FINE)) {
        debug.fine(" Returning false");
      }
      return false;
    }

    if (debug.isLoggable(Level.FINE)) {
      debug.fine(" Returning true");
    }

    return true;
  }
  // Put this in its own method to have fewer branches in KeY proof
  @Pure
  private boolean shouldPrintBasedOnRel(int rel) {
    if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2
            || rel == DetailedStatisticsVisitor.REL_SAME_UNJUST1_UNJUST2
            || rel == DetailedStatisticsVisitor.REL_DIFF_UNJUST1_UNJUST2
            || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST1
            || rel == DetailedStatisticsVisitor.REL_MISS_UNJUST2) {
      if (debug.isLoggable(Level.FINE)) {
        debug.fine(" Returning false");
      }

      return false;
    }
    return true;
  }
}
