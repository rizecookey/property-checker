package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class PptSlice0 extends PptSlice {

  static final long serialVersionUID = 20020122L;

  PptSlice0(PptTopLevel parent) {}

  /*@helper@*/ public final int arity() {}

  public static PptSlice makeFakePrestate(PptSlice sliceTemplate) {}

  public void checkRep() {}

  public void addInvariant(Invariant inv) {}

  public void removeInvariant(Invariant inv) {}

  public void removeInvariants(List to_remove) {}

  public boolean hasImplication(Implication imp) {}

  public int num_samples() {}

  public int num_mod_samples() {}

  public int num_values() {}

  void instantiate_invariants() {}

  public List add(ValueTuple vt, int count) {}
}
