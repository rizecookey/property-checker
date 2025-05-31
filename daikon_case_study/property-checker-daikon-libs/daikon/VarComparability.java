package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public abstract class VarComparability {

  //public static final Logger debug = Logger.getLogger("daikon.VarComparability");

  public static final int NONE = 0;
  public static final int IMPLICIT = 1;

  public static VarComparability parse(int format, String rep, ProglangType vartype) {}

  public static VarComparability makeComparabilitySameIndices(String elemTypeName, VarComparability old) {}

  public static VarComparability makeAlias(VarInfo vi) {}

  public abstract VarComparability makeAlias();

  public abstract VarComparability elementType();

  public abstract VarComparability indexType(int dim);

  public abstract VarComparability string_length_type();

  public abstract boolean alwaysComparable();

  /*@pure@*/ public static boolean comparable(VarInfo v1, VarInfo v2) {}

  /*@pure@*/ public static boolean comparable(VarComparability type1, VarComparability type2) {}

  public boolean equality_set_ok(VarComparability other) {}
}
