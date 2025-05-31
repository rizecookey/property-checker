package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public abstract class Joiner extends Invariant {

  static final long serialVersionUID = 20030822L;

  public Invariant left;
  public Invariant right;

  protected Joiner(PptSlice ppt) {}

  Joiner(PptSlice ppt, Invariant left, Invariant right) {}

  protected Joiner(PptTopLevel ppt, Invariant left, Invariant right) {}

  public abstract String repr();

  protected Invariant resurrect_done(int[] permutation) {}

  public abstract String format_using(OutputFormat format);

  /*@pure@*/ public boolean isValidEscExpression() {}

  /*@pure@*/ public boolean isObviousDerived() {}

  /*@pure@*/ public /*@nullable@*/ DiscardInfo isObviousImplied() {}

  /*@pure@*/ public boolean isSameInvariant(Invariant other) {}

  /*@pure@*/ public boolean isSameFormula(Invariant other) {}
}
