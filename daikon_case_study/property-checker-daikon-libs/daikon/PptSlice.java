package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public abstract class PptSlice extends Ppt {

  static final long serialVersionUID = 20040921L;
  protected static final String lineSep = Global.lineSep;
  //public static final Logger debug = Logger.getLogger("daikon.PptSlice");
  //public static final Logger debugGeneral = Logger.getLogger("daikon.PptSlice.general");
  //public static final Logger debugFlow = Logger.getLogger("daikon.flow.flow");
  //public static final Logger debugGuarding = Logger.getLogger("daikon.guard");
  public PptTopLevel parent;

  /*@ public normal_behavior
    @ ensures 0 <= \result && \result <= 3;
    @ assignable \strictly_nothing;
    @*/
  /*@helper@*/ public abstract int arity();

  /*@ public normal_behavior
    @ assignable \everything;
    @*/
  /*@helper@*/ public abstract void addInvariant(Invariant inv);

  /*@ public normal_behavior
    @ assignable \everything;
    @*/
  /*@helper@*/ public void removeInvariant(Invariant inv) {}

  public List invs;

  PptSlice(PptTopLevel parent, VarInfo[] var_infos) {}

  /*@ public normal_behavior
    @ assignable \strictly_nothing;
    @*/
  /*@helper@*/ public final String name() {}

  public boolean usesVar(VarInfo vi) {}

  public boolean usesVar(String name) {}

  public boolean usesVarDerived(String name) {}

  public boolean allPrestate() {}


  public void removeInvariants(List to_remove) {}

  abstract List add(ValueTuple full_vt, int count);

  // @RequiresNonNull("daikon.suppress.NIS.suppressor_map")
  protected void remove_falsified() {}

  public abstract int num_samples();

  public abstract int num_values();

  abstract void instantiate_invariants();

  public static final class ArityVarnameComparator {}

  public static final class ArityPptnameComparator {}

  public boolean containsOnlyGuardingPredicates() {}

  public void processOmissions(boolean[] omitTypes) {}

  public void repCheck() {}

  PptSlice cloneAndPivot(VarInfo[] newVis) {}

  public PptSlice copy_new_invs(PptTopLevel ppt, VarInfo[] vis) {}

  public boolean contains_inv(Invariant inv) {}

  // @EnsuresNonNullIf(result = true, expression = "find_inv_exact(#1)")
  public boolean contains_inv_exact(Invariant inv) {}

  /*@pure@*/ public /*@nullable@*/ Invariant find_inv_exact(Invariant inv) {}

  public /*@nullable@*/ Invariant find_inv_by_class(Class cls) {}

  /*@pure@*/ public boolean is_inv_true(Invariant inv) {}

  public void log(String msg) {}
}
