package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class ValueTuple implements Cloneable {

  //public static Logger debug = Logger.getLogger("daikon.ValueTuple");

  public /*@nullable@*/ Object[] vals;
  public int[] mods;
  public static final int UNMODIFIED = 0;
  public static final int MODIFIED = 1;
  public static final int MISSING_NONSENSICAL = 2;
  public static final int MISSING_FLOW = 3;
  public static final int MODBIT_VALUES = 4;
  public static final int STATIC_CONSTANT = 22;

  /*@pure@*/ public int getModified(VarInfo vi) {}

  /*@pure@*/ public boolean isUnmodified(VarInfo vi) {}

  /*@pure@*/ public boolean isModified(VarInfo vi) {}

  /*@pure@*/ public boolean isMissingNonsensical(VarInfo vi) {}

  /*@pure@*/ public boolean isMissingFlow(VarInfo vi) {}

  // @EnsuresNonNullIf(result = false, expression = "vals[#1.value_index]")
  /*@pure@*/ public boolean isMissing(VarInfo vi) {}

  /*@pure@*/ int getModified(int value_index) {}

  /*@pure@*/ boolean isUnmodified(int value_index) {}

  /*@pure@*/ boolean isModified(int value_index) {}

  /*@pure@*/ /*@helper@*/ boolean isMissingNonsensical(int value_index) {}

  /*@pure@*/ /*@helper@*/ boolean isMissingFlow(int value_index) {}

  // @EnsuresNonNullIf(result = false, expression = "vals[#1]")
  /*@pure@*/ /*@helper@*/ boolean isMissing(int value_index) {}

  /*@pure@*/
  static boolean modIsUnmodified(int mod_value) {}

  /*@pure@*/ static boolean modIsModified(int mod_value) {}

  /*@pure@*/ static boolean modIsMissingNonsensical(int mod_value) {}

  /*@pure@*/ static boolean modIsMissingFlow(int mod_value) {}

  public static final int TUPLEMOD_VALUES;
  public static final int UNMODIFIED_BITVAL;
  public static final int MODIFIED_BITVAL;
  public static final int MISSING_NONSENSICAL_BITVAL;
  public static final int MISSING_FLOW_BITVAL;
  public static final int[] tuplemod_not_missing;
  public static final int[] tuplemod_modified_not_missing;

  static int make_tuplemod(boolean unmodified, boolean modified, boolean missingNonsensical, boolean missingFlow) {}

  static boolean tuplemodHasModified(int tuplemod) {}

  static boolean tuplemodHasUnmodified(int tuplemod) {}

  static boolean tuplemodHasMissingNonsensical(int tuplemod) {}

  static boolean tuplemodHasMissingFlow(int tuplemod) {}

  static String tuplemodToStringBrief(int tuplemod) {}

  static int tupleMod(int[] mods) {}

  int tupleMod() {}

  public static int parseModified(String raw) {}

  public Object getValue(VarInfo vi) {}

  public /*@nullable@*/ Object getValueOrNull(VarInfo vi) {}

  Object getValue(int val_index) {}

  /*@nullable@*/ Object getValueOrNull(int val_index) {}

  /*@pure@*/ /*@helper@*/ public void checkRep() {}

  public ValueTuple(/*@nullable@*/ Object[] vals, int[] mods) {}

  private ValueTuple(/*@nullable@*/ Object[] vals, int[] mods, boolean check) {}

  public static ValueTuple makeUninterned(/*@nullable@*/ Object[] vals, int[] mods) {}

  static ValueTuple makeFromInterned(/*@nullable@*/ Object[] vals, int[] mods) {}

  public ValueTuple shallowcopy() {}

  /*@pure@*/ public int size() {}

  public ValueTuple trim(int len) {}

  public ValueTuple slice(int[] indices) {}
}
