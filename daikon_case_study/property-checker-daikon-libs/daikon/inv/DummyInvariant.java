package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public class DummyInvariant extends Invariant {

  static final long serialVersionUID = 20030220L;
  public boolean valid = false;

  public DummyInvariant(
      PptSlice ppt,
      /*@nullable@*/ String daikonStr,
      /*@nullable@*/ String java,
      /*@nullable@*/ String esc,
      /*@nullable@*/ String simplify,
      /*@nullable@*/ String jml,
      /*@nullable@*/ String dbc,
      /*@nullable@*/ String csharp,
      boolean valid) {}

  public DummyInvariant(
      /*@nullable@*/ String daikonStr,
      /*@nullable@*/ String java,
      /*@nullable@*/ String esc,
      /*@nullable@*/ String simplify,
      /*@nullable@*/ String jml,
      /*@nullable@*/ String dbc,
      /*@nullable@*/ String csharp,
      boolean valid) {}

  public DummyInvariant instantiate(PptTopLevel parent, VarInfo[] vars) {}

  protected double computeConfidence() {}

  public void negate() {}

  public String format_using(OutputFormat format) {}

  public String format_daikon() {}

  public String format_java() {}

  public String format_esc() {}

  public String format_simplify() {}

  public String format_jml() {}

  public String format_dbc() {}

  public String format_csharp() {}

  protected Invariant resurrect_done(int[] permutation) {}

  public boolean isSameFormula(Invariant other) {}

  public boolean enabled() {}

  public boolean valid_types(VarInfo[] vis) {}

  protected DummyInvariant instantiate_dyn(PptSlice slice) {}

  public /*@nullable@*/ DummyInvariant merge(List invs, PptSlice parent_ppt) {}
}
