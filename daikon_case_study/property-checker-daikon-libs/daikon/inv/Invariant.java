package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public abstract class Invariant implements Cloneable {

  static final long serialVersionUID = 20040921L;

  //public static final Logger debug = Logger.getLogger("daikon.inv.Invariant");
  //public static final Logger debugPrint = Logger.getLogger("daikon.print");
  //public static final Logger debugFlow = Logger.getLogger("daikon.flow.flow");
  //public static final Logger debugPrintEquality = Logger.getLogger("daikon.print.equality");
  //public static final Logger debugIsWorthPrinting = Logger.getLogger("daikon.print.isWorthPrinting");
  //public static final Logger debugGuarding = Logger.getLogger("daikon.guard");
  //public static final Logger debugIsObvious = Logger.getLogger("daikon.inv.Invariant.isObvious");

  public static double dkconfig_confidence_limit = .99;
  public static boolean dkconfig_simplify_define_predicates = false;
  public static double dkconfig_fuzzy_ratio = 0.0001;
  public static boolean invariantEnabledDefault = true;
  public PptSlice ppt;
  protected boolean falsified = false;
  public boolean isGuardingPredicate = false;
  public static final double CONFIDENCE_JUSTIFIED = 1;
  public static final double CONFIDENCE_UNJUSTIFIED = 0;
  public static final double CONFIDENCE_NEVER = -1;
  public static final double PROBABILITY_JUSTIFIED = 0;
  public static final double PROBABILITY_UNJUSTIFIED = 1;
  public static final double PROBABILITY_NEVER = 3;

  public static final double conf_is_ge(double x, double goal) {}

  public static final double prob_is_ge(double x, double goal) {}

  public static final double confidence_and(double c1, double c2) {}

  public static final double confidence_and(double c1, double c2, double c3) {}

  public static final double confidence_or(double c1, double c2) {}

  public static final double prob_and(double p1, double p2) {}

  public static final double prob_and(double p1, double p2, double p3) {}

  public static final double prob_or(double p1, double p2) {}

  public static final int min_mod_non_missing_samples = 5;

  public boolean enoughSamples() {}

  /*@ public normal_behavior
    @ assignable \nothing;
    @*/
  public final /*@helper@*/ boolean justified() {}

  /*@ public normal_behavior
    @ ensures 0.0 <= \result && \result <= 1.0;
    @ assignable \nothing;
    @*/
  public final /*@helper@*/ double getConfidence() {}

  protected abstract double computeConfidence();

  /*@pure@*/ public boolean isExact() {}

  protected Invariant(PptSlice ppt) {}

  protected Invariant() {}

  public void falsify() {}

  public void clear_falsified() {}

  /*@pure@*/ public boolean is_false() {}

  public Invariant transfer(PptSlice new_ppt, int[] permutation) {}

  public Invariant clone_and_permute(int[] permutation) {}

  public Invariant resurrect(PptSlice new_ppt, int[] permutation) {}

  public VarComparability get_comparability() {}

  public /*@nullable@*/ Invariant merge(List invs, PptSlice parent_ppt) {}

  public Invariant permute(int[] permutation) {}

  protected abstract Invariant resurrect_done(int[] permutation);

  public boolean usesVar(VarInfo vi) {}

  public boolean usesVar(String name) {}

  public boolean usesVarDerived(String name) {}

  public final String varNames() {}

  /*@ public normal_behavior
    @ assignable \nothing;
    @*/
  public /*@helper@*/ String repr() {}

  /*@ public normal_behavior
    @ assignable \nothing;
    @*/
  public /*@helper@*/ boolean isWorthPrinting() {}

  /*@ public normal_behavior
    @ assignable \everything;
    @*/
  public abstract /*@helper@*/ String format_using(OutputFormat format);

  public String repr_prob() {}

  public String format() {}

  public String format_classname() {}


  public boolean isValidEscExpression() {}

  public boolean isValidExpression(OutputFormat format) {}

  public String format_unimplemented(OutputFormat format) {}

  public String format_too_few_samples(OutputFormat format, /*@nullable@*/ String attempt) {}

  public static String simplify_format_double(double d) {}

  public static String simplify_format_long(long l) {}

  public static String simplify_format_string(String s) {}

  public static final class InvariantComparatorForPrinting implements Comparator {

    /*@pure@*/ public int compare(Invariant inv1, Invariant inv2) {}
  }

  public abstract boolean isSameFormula(Invariant other);

  public boolean mergeFormulasOk() {}

  /*@ public normal_behavior
    @ assignable \nothing;
    @*/
  public /*@helper@*/ boolean isSameInvariant(Invariant inv2) {}

  /*@pure@*/ public boolean isExclusiveFormula(Invariant other) {}

  public static /*@nullable@*/ Invariant find(Class invclass, PptSlice ppt) {}

  ///*@pure@*/ public /*@nullable@*/ NISuppressionSet get_ni_suppressions() {}

  // @EnsuresNonNullIf(result = true, expression = "get_ni_suppressions()")
  /*@pure@*/ public boolean is_ni_suppressed() {}

  /*@pure@*/ public final /*@nullable@*/ DiscardInfo isObviousStatically() {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousStatically(VarInfo[] vis) {}

  /*@pure@*/ public boolean isObviousStatically_AllInEquality() {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousStatically_SomeInEquality() {}

  /*@pure@*/ protected /*@nullable@*/ DiscardInfo isObviousStatically_SomeInEqualityHelper(VarInfo[] vis, VarInfo[] assigned, int position) {}

  /*@pure@*/ public final /*@nullable@*/ DiscardInfo isObvious() {}

  public /*@nullable@*/ DiscardInfo isObviousDynamically(VarInfo[] vis) {}

  /*@pure@*/ public boolean isReflexive() {}

  public final /*@nullable@*/ DiscardInfo isObviousDynamically() {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousDynamically_SomeInEquality() {}

  protected /*@nullable@*/ DiscardInfo isObviousDynamically_SomeInEqualityHelper(VarInfo[] vis, VarInfo[] assigned, int position) {}

  /*@pure@*/ public boolean isAllPrestate() {}

  public boolean hasUninterestingConstant() {}

  public static final class ClassVarnameComparator implements Comparator {
    /*@pure@*/ public int compare(Invariant inv1, Invariant inv2) {}
  }

  public static final class ClassVarnameFormulaComparator implements Comparator {

    ClassVarnameFormulaComparator classVarnameComparator = new ClassVarnameComparator();

    /*@pure@*/ public int compare(Invariant inv1, Invariant inv2) {}
  }

  public static class Match {

    public Invariant inv;

    public Match(Invariant inv) {}
  }

  public boolean match(Invariant inv) {}

  public boolean state_match(Object state) {}

  public /*@nullable@*/ Invariant createGuardingPredicate(boolean install) {}

  public List getGuardingList() {}

  public static List getGuardingList(VarInfo[] varInfos) {}

  public /*@nullable@*/ Invariant createGuardedInvariant(boolean install) {}

  protected abstract Invariant instantiate_dyn(PptSlice slice);

  public abstract boolean enabled();

  public abstract boolean valid_types(VarInfo[] vis);

  public boolean instantiate_ok(VarInfo[] vis) {}

  public /*@nullable@*/ Invariant instantiate(PptSlice slice) {}

  public InvariantStatus add_sample(ValueTuple vt, int count) {}

  public void repCheck() {}

  /*@pure@*/ public boolean isActive() {}

  public static boolean logDetail() {}

  public static boolean logOn() {}

  //public void log(Logger log, String msg) {}

  /*@pure@*/ /*@helper@*/ public boolean log(String format, /*@nullable@*/ Object[] args) {}

  public static String toString(Invariant[] invs) {}

  public static String formatFuzzy(String method, VarInfo v1, VarInfo v2, OutputFormat format) {}

  public static Class asInvClass(Object x) {}

  public boolean isEqualityComparison() {}

  public void checkRep() {}

  public static Map checkedMergeOverridden;
}
