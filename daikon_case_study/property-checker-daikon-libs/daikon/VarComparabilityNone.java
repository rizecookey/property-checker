package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class VarComparabilityNone extends VarComparability {

  static final long serialVersionUID = 20020122L;

  public static final VarComparabilityNone it = new VarComparabilityNone();

  private VarComparabilityNone() {}

  static VarComparabilityNone parse(String rep, ProglangType vartype) {}

  public VarComparability makeAlias() {}

  public VarComparability elementType() {}

  public VarComparability indexType(int dim) {}

  public VarComparability string_length_type() {}

  public boolean alwaysComparable() {}

  /*@pure@*/
  static boolean comparable(VarComparabilityNone vcomp1, VarComparabilityNone vcomp2) {}
}
