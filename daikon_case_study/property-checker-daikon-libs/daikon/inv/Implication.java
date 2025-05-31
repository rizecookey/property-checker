package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public class Implication extends Joiner {

  static final long serialVersionUID = 20030822L;

  public Invariant predicate() {}

  public Invariant consequent() {}

  public boolean iff;

  protected Implication(PptSlice ppt, Invariant predicate, Invariant consequent, boolean iff, Invariant orig_predicate, Invariant orig_consequent) {}

  public static /*@nullable@*/ Implication makeImplication(PptTopLevel ppt, Invariant predicate, Invariant consequent, boolean iff, Invariant orig_predicate, Invariant orig_consequent) {}

  protected double computeConfidence() {}

  public String repr() {}

  public String format_using(OutputFormat format) {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousStatically(VarInfo[] vis) {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousDynamically(VarInfo[] vis) {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousStatically_SomeInEquality() {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousDynamically_SomeInEquality() {}

  /*@pure@*/
  public boolean isSameFormula(Invariant other) {}

  /*@ public normal_behavior
    @ ensures \result ==> other != null;
    @ assignable \nothing;
    @*/
  public boolean isSameInvariant(Invariant other) {}

  public boolean hasUninterestingConstant() {}

  /*@pure@*/ public boolean isAllPrestate() {}

  // public void log(Logger log, String msg) {}

  /*@helper@*/ public boolean log(String format, /*@nullable@*/ Object[] args) {}

  public boolean enabled() {}

  public boolean valid_types(VarInfo[] vis) {}

  protected Invariant instantiate_dyn(PptSlice slice) {}

  public /*@nullable@*/ Implication merge(List invs, PptSlice parent_ppt) {}
}
