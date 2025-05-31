package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class ProglangType {

  static final long serialVersionUID = 20020122L;

  public static Set list_implementors;

  public static boolean dkconfig_convert_to_signed = false;

  public String base() {}

  public int dimensions() {}

  /*@pure@*/ public boolean isArray() {}

  private ProglangType(String basetype, int dimensions) {}

  public static ProglangType parse(String rep) {}

  public static ProglangType rep_parse(String rep) {}

  public ProglangType fileTypeToRepType() {}

  //public Object readResolve() throws ObjectStreamException {}

  public ProglangType elementType() {}

  public static final ProglangType INT;
  public static final ProglangType LONG_PRIMITIVE;
  public static final ProglangType DOUBLE;
  public static final ProglangType CHAR;
  public static final ProglangType STRING;
  public static final ProglangType INT_ARRAY;
  public static final ProglangType LONG_PRIMITIVE_ARRAY;
  public static final ProglangType DOUBLE_ARRAY;
  public static final ProglangType CHAR_ARRAY;
  public static final ProglangType STRING_ARRAY;
  public static final ProglangType CHAR_ARRAY_ARRAY;
  public static final ProglangType INTEGER;
  public static final ProglangType LONG_OBJECT;
  public static final ProglangType OBJECT;
  public static final ProglangType BOOLEAN;
  public static final ProglangType HASHCODE;
  public static final ProglangType BOOLEAN_ARRAY;
  public static final ProglangType HASHCODE_ARRAY;


  //public final /*@nullable@*/ Object parse_value(String value, LineNumberReader reader, String filename) {}

  //public final /*@nullable@*/ Object parse_value_scalar(String value, LineNumberReader reader, String filename) {}

  //public final /*@nullable@*/ Object parse_value_array_1d(String value, LineNumberReader reader, String filename) {}

  //public final /*@nullable@*/ Object parse_value_array_2d(String value, LineNumberReader reader, String filename) {}

  public boolean baseIsPrimitive() {}

  /*@pure@*/ public boolean isPrimitive() {}

  public boolean baseIsIntegral() {}

  /*@pure@*/ public boolean isIntegral() {}

  public boolean elementIsIntegral() {}

  public boolean elementIsFloat() {}

  public boolean elementIsString() {}

  /*@pure@*/ public boolean isIndex() {}

  /*@pure@*/
  public boolean isScalar() {}

  public boolean baseIsScalar() {}

  public boolean baseIsBoolean() {}

  public boolean baseIsFloat() {}

  /*@pure@*/ public boolean isFloat() {}

  /*@pure@*/ public boolean isObject() {}

  public boolean baseIsObject() {}

  public boolean baseIsString() {}

  public boolean baseIsHashcode() {}

  public boolean isHashcode() {}

  public boolean isPointerFileRep() {}

  public boolean comparableOrSuperclassEitherWay(ProglangType other) {}

  public boolean comparableOrSuperclassOf(ProglangType other) {}

  public String format() {}

  /*@pure@*/ public boolean is_function_pointer() {}
}
