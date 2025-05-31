package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public final class Equality extends Invariant {

  static final long serialVersionUID = 20021231L;
  //public static final Logger debug = Logger.getLogger("daikon.inv.Equality");
  //public static final Logger debugPostProcess = Logger.getLogger("daikon.inv.Equality.postProcess");

  public void setSamples(int sample_cnt) {}

  public int numSamples() {}

  /*@pure@*/ public int size() {}

  public Set getVars() {}

  public Equality(Collection variables, PptSlice ppt) {}

  /*@pure@*/ public VarInfo leader() {}

  public boolean hasNonCanonicalVariable() {}

  public double computeConfidence() {}

  public String repr() {}

  public String format_using(OutputFormat format) {}

  public String format_daikon() {}

  public String format_java() {}

  public String format_esc() {}

  public String format_simplify() {}

  public String shortString() {}

  public String format_java_family(OutputFormat format) {}

  public List add(ValueTuple vt, int count) {}

  protected Invariant resurrect_done(int[] permutation) {}

  /*@pure@*/ public boolean isSameFormula(Invariant other) {}

  public void postProcess() {}

  public void pivot() {}

  public void repCheck() {}

  public boolean enabled() {}

  public boolean valid_types(VarInfo[] vis) {}

  protected Equality instantiate_dyn(PptSlice slice) {}

  public /*@nullable@*/ Equality merge(List invs, PptSlice parent_ppt) {}
}
