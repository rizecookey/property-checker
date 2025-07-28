package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class VarComparabilityImplicit extends VarComparability {

  static final long serialVersionUID = 20020122L;

  int base;

  VarComparabilityImplicit[] indexTypes;

  int dimensions;

  public static final VarComparabilityImplicit unknown = new VarComparabilityImplicit(-3, null, 0);

  private VarComparabilityImplicit(int base, VarComparabilityImplicit[] indexTypes, int dimensions) {}

  public boolean baseAlwayscomparable() {}

  /*@pure@*/ public boolean alwaysComparable() {}

  static VarComparabilityImplicit parse(String rep, /*@nullable@*/ ProglangType vartype) {}

  public VarComparability makeAlias() {}

  public VarComparability elementType() {}

  public VarComparability string_length_type() {}

  /*@pure@*/ public VarComparability indexType(int dim) {}

  /*@pure@*/ static boolean comparable(VarComparabilityImplicit type1, VarComparabilityImplicit type2) {}

  public boolean equality_set_ok(VarComparability other) {}
}
