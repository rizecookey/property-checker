package daikon.diff;

import daikon.PptConditional;
import daikon.PptSlice;
import daikon.PptTopLevel;
import daikon.inv.Invariant;
import daikon.inv.OutputFormat;
import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.StringTokenizer;
import org.checkerframework.checker.nullness.qual.EnsuresNonNullIf;
import org.checkerframework.checker.nullness.qual.*;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/**
 * MatchCountVisitor is a visitor that almost does the opposite of PrintDifferingInvariantsVisitor.
 * MatchCount prints invariant pairs if they are the same, and only if they are a part of a
 * conditional ppt. The visitor also accumulates some state during its traversal for statistics, and
 * can report the match precision.
 *
 * @author Lee Lin
 */
public class MatchCountVisitor extends PrintAllVisitor {

  // invariants found by the splitting
  private HashSet<String> cnt = new HashSet<>();
  // target set of invariants
  private HashSet<String> targSet = new HashSet<>();
  // invariants found matching
  private HashSet<String> recall = new HashSet<>();

  private HashMap<String, HashSet<String>> goodMap = new HashMap<>();

  public MatchCountVisitor(PrintStream ps, boolean verbose, boolean printEmptyPpts) {
    super(ps, verbose, printEmptyPpts);
  }

  // throw out Program points that are not Conditional,
  // meaning they were NOT added from our splitters
  @Override
  public void visit(@NonNullNode PptNode node) {
    PptTopLevel ppt = node.getPpt1();
    if (!(ppt instanceof PptConditional)) {
      return;
    } else {
      super.visit(node);
    }
  }

  @Override
  public void visit(@NonNullNode InvNode node) {
    Invariant inv1 = node.getInv1();
    Invariant inv2 = node.getInv2();

    String key1 = visitInv1(inv1);
    String key2 = visitInv2(inv2);

    // :: error: nullnessnode.argument.type.incompatible
    if (shouldPrint(inv1, inv2)) {
      // inv1 and inv2 should be the same, so it doesn't matter
      // which one we choose when adding to recall -LL
      @NonNull HashSet<String> recallLocal = recall;
      recallLocal.add(key1);

      // System.out.println("K1: " + key1);
      // System.out.println ("K2: " + key2);

      @NonNull PptSlice ppt1 = inv1.ppt;
      @NonNull String thisPptName1 = ppt1.name();
      // System.out.println ("NAME1: " + thisPptName1);
      // Contest.smallestRoom(II)I:::EXIT;condition="not(max <= num)"

      //TODO Comment this out for now, since KeY does not support lambdas

      /*
      String bucketKey = thisPptName1.substring(0, thisPptName1.lastIndexOf(";condition"));
      String predicate = extractPredicate(thisPptName1);
      HashSet<String> bucket = goodMap.computeIfAbsent(bucketKey, __ -> new HashSet<String>());
      bucket.add(predicate + " ==> " + inv1.format());
      */
    }
  }
  // Split into multiple methods to make KeY proofs easier
  private String visitInv1(@Nullable Invariant inv1) {
    String key1 = "";
    if (inv1 != null && inv1.justified() && !filterOut(inv1)) {
      key1 = buildKey(inv1, ";condition");

      // checks for justification
      // :: error: nullnessnode.argument.type.incompatible
      if (shouldPrint(inv1, inv1)) { // [???]
        @NonNull HashSet<String> cntLocal = cnt;
        cntLocal.add(key1);
      }
    }
    return key1;
  }
  private String visitInv2(@Nullable Invariant inv2) {
    String key2 = "";
    if (inv2 != null && inv2.justified() && !filterOut(inv2)) {
      key2 = buildKey(inv2, "(");
      @NonNull HashSet<String> targSetLocal = targSet;
      targSetLocal.add(key2);
    }
    return key2;
  }
  private String buildKey(Invariant inv, String endMarker) {
    String thisPptName = inv.ppt.name();
    String thisPptName_substring = thisPptName.substring(0, thisPptName.lastIndexOf(endMarker));
    return thisPptName_substring + "$" + inv.format_using(OutputFormat.JAVA);
  }

  /** Grabs the splitting condition from a pptname. */
  private String extractPredicate(String s) {
    int cut = s.indexOf(";condition=");
    return s.substring(cut + 12, s.lastIndexOf('"'));
  }

  /** Returns true if the pair of invariants should be printed. */
  @EnsuresNonNullIf(
      result = true,
      expression = {"#1", "#2"})
  // :: error: nullnessnode.contracts.postcondition.not.satisfied
  protected static boolean shouldPrint(@NonNullIfNull("inv2") @Nullable Invariant inv1, @NonNullIfNull("inv1") @Nullable Invariant inv2) {
    // :: error: nullnessnode.argument.type.incompatible
    int rel = DetailedStatisticsVisitor.determineRelationship(inv1, inv2);
    if (rel == DetailedStatisticsVisitor.REL_SAME_JUST1_JUST2) {
      // determineRelationship returns REL_SAME_JUST1_JUST2 only if inv1 and inv2 are nonnull
      //assert inv1 != null : "@AssumeAssertion(nullness): dependent: called determineRelationship()";
      //assert inv2 != null : "@AssumeAssertion(nullness): dependent: called determineRelationship()";

      // got rid of unjustified
      //   rel == DetailedStatisticsVisitor.REL_SAME_UNJUST1_UNJUST2)

      // Added to get rid of constants other than -1, 0, 1 in the
      // invariant's format_java() string... this change was made to
      // filter out targets that could never really be achived
      // example:   num >= 10378

      // :: error: nullness.argument.type.incompatible
      if (filterOut(inv1) || filterOut(inv2)) {
        return false;
      }

      // now you have a match
      return true;
    }

    return false;
  }

  /**
   * Returns true iff any token of {@code inv.format_java()} contains a number other than -1, 0, 1
   * or is null.
   */
  private static boolean filterOut(Invariant inv) {
    //assert inv != null : "@AssumeAssertion(nullness): precondition";
    String str = inv.format_using(OutputFormat.JAVA);
    StringTokenizer st = new StringTokenizer(str, " ()");
    while (st.hasMoreTokens()) {
      String oneToken = st.nextToken();
      try {
        char firstChar = oneToken.charAt(0);
        // remember identifiers can not begin with [0-9\-]
        if (Character.isDigit(firstChar) || firstChar == '-') {
          if (acceptableNumber(oneToken)) {
            // continue;
          } else {
            return true;
          }
        }

      } catch (NumberFormatException e) {
        System.out.println(
            "Should never get here... NumberFormatException in filterOut: " + oneToken);
        // continue;
      }
    }
    return false;
  }

  public double calcRecall() {
    System.out.println("Recall: " + recall.size() + " / " + targSet.size());
    if (targSet.size() == 0) {
      // avoids divide by zero
      return -1;
    }
    return (double) recall.size() / targSet.size();
  }

  /**
   * Returns true iff numLiteral represents a numeric literal string of integer or float that we
   * believe will be useful for a splitting condition. Usually that includes -1, 0, 1, and any other
   * numeric literal found in the source code.
   */
  private static boolean acceptableNumber(String numLiteral) {

    // need to make sure that it is an integer vs. floating
    // point number

    // could be float, look for "."
    if (numLiteral.indexOf(".") > -1) {
      // float fnum = Float.parseFloat(numLiteral);
      // for now, accept all floats (ignore return value of parseFloat)
      return true;
    }
    // not float, must be int
    else {
      int num = Integer.parseInt(numLiteral);

      // accept -1, 0, 1
      return (num == -1 || num == 0 || num == 1);
    }
  }

  public double calcPrecision() {

    System.out.println("Prec: " + recall.size() + " / " + cnt.size());
    if (cnt.size() == 0) {
      // to avoid a divide by zero
      return -1;
    }
    return (double) recall.size() / cnt.size();
  }

  /** Prints the results of the correct set in a human-readable format. */
  public void printFinal() {
    for (String ppt : goodMap.keySet()) {
      System.out.println();
      System.out.println("*****************" + ppt);
      for (String s : goodMap.get(ppt)) {
        System.out.println(s);
      }
    }
  }
}
