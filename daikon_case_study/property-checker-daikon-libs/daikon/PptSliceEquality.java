package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class PptSliceEquality extends PptSlice {

  static final long serialVersionUID = 20021231L;

  public static boolean dkconfig_set_per_var = false;
  //public static final Logger debug = Logger.getLogger("daikon.PptSliceEquality");
  //public static final Logger debugGlobal = Logger.getLogger("daikon.PptSliceEquality.Global");

  PptSliceEquality(PptTopLevel parent) {}

  /*@helper@*/ public final int arity() {}

  void init_po() {}

  public void addInvariant(Invariant inv) {}

  /*@helper@*/ public int num_samples() {}

  public int num_mod_samples() {}

  public int num_values() {}

  void instantiate_invariants() {}

  public void instantiate_from_pairs(Set eset) {}

  public List add(ValueTuple vt, int count) {}

  public List createEqualityInvs(List vis, Equality leader) {}

  public List copyInvsFromLeader(VarInfo leader, List newVis) {}

  public void repCheck() {}

  public static final class EqualityComparator {

    public static final EqualityComparator theInstance = new EqualityComparator();
  }

  public VarInfo[] get_leaders_sorted() {}
}
