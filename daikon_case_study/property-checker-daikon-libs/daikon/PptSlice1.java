package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class PptSlice1 extends PptSlice {

  static final long serialVersionUID = 20040921L;

  //public static final Logger debugSpecific = Logger.getLogger("daikon.PptSlice1");
  //public static final Logger debugMerge = Logger.getLogger("daikon.PptSlice.merge");

  public PptSlice1(PptTopLevel parent, VarInfo[] var_infos) {}

  PptSlice1(PptTopLevel parent, VarInfo var_info) {}

  /*@helper@*/public final int arity() {}

  public void instantiate_invariants() {}

  public void instantiate_invariants(List proto_invs) {}

  public int num_samples() {}

  public int num_values() {}

  public List add(ValueTuple full_vt, int count) {}

  public List add_val_bu(Object val1, int mod1, int count) {}

  public void addInvariant(Invariant invariant) {}

  protected PptSlice cloneAndPivot(VarInfo[] argNewVarInfos) {}

  public void merge_invariants() {}
}
