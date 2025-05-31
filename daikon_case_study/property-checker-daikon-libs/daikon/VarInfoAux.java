package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class VarInfoAux implements Cloneable {

  static final long serialVersionUID = 20020614L;

  //public static final Logger debug = Logger.getLogger("daikon.VarInfoAux");
  public static final String TRUE = "true";
  public static final String FALSE = "false";
  public static final String NULL_TERMINATING = "nullTerminating";
  public static final String IS_PARAM = "isParam";
  public static final String HAS_DUPLICATES = "hasDuplicates";
  public static final String HAS_ORDER = "hasOrder";
  public static final String HAS_SIZE = "hasSize";
  public static final String HAS_NULL = "hasNull";
  public static final String MINIMUM_LENGTH = "minlength";
  public static final String MAXIMUM_LENGTH = "maxlength";
  public static final String MINIMUM_VALUE = "minvalue";
  public static final String MAXIMUM_VALUE = "maxvalue";
  public static final String VALID_VALUES = "validvalues";
  public static final String IS_STRUCT = "isStruct";
  public static final String IS_NON_NULL = "isNonNull";
  public static final String PACKAGE_NAME = "declaringClassPackageName";
  public static final String NO_PACKAGE_NAME = "no_package_name_string";

  private VarInfoAux() {}

  private VarInfoAux(Map map) {}

  public static VarInfoAux parse(String inString) throws IOException {}

  public static VarInfoAux getDefault() {}

  /*@pure@*/ public boolean equalsVarInfoAux(VarInfoAux o) {}

  /*@pure@*/ public boolean equals_for_instantiation(VarInfoAux o) {}

  /*@pure@*/ public int getInt(String key) {}

  public String[] getList(String key) {}

  public String getValue(String key) {}

  public /*@nullable@*/ String getValueOrNull(String key) {}

  // @EnsuresKeyForIf(result = true, expression = "#1", map = "map")
  /*@pure@*/
  public boolean hasValue(String key) {}

  public boolean getFlag(String key) {}

  public VarInfoAux setValue(String key, String value) {}

  public VarInfoAux setInt(String key, int value) {}

  /*@pure@*/ public boolean nullTerminating() {}

  /*@pure@*/ public boolean isParam() {}

  /*@pure@*/ public boolean packageName() {}

  /*@pure@*/ public boolean hasDuplicates() {}

  /*@pure@*/ public boolean hasOrder() {}

  /*@pure@*/ public boolean hasSize() {}

  /*@pure@*/ public boolean hasNull() {}

  /*@pure@*/ public boolean isStruct() {}

  /*@pure@*/ public boolean isNonNull() {}
}
