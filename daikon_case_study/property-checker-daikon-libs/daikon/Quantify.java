package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class Quantify {

  public enum QuantFlags {
    ELEMENT_WISE,
    ADJACENT,
    DISTINCT,
    INCLUDE_INDEX;
    public static Set element_wise() {}
    public static Set adjacent() {}
    public static Set distinct() {}
    public static Set include_index() {}
  }

  public static Set get_flags(boolean elementwise) {}

  public abstract static class Term {
    public abstract String name();

    public String esc_name() {}

    public String jml_name() {}

    public String jml_name(boolean in_prestate) {}

    public String simplify_name() {}

    public String csharp_name() {}

    protected static String name_with_offset(String name, int offset) {}
  }

  public static class FreeVar extends Term {
    String name;

    public FreeVar(String name) {}

    public String name() {}

    public String simplify_name() {}
  }

  public static class Constant extends Term {
    int val;

    public Constant(int val) {}

    public String name() {}

    public int get_value() {}
  }

  public static class Length extends Term {
    VarInfo sequence;
    int offset;

    public Length(VarInfo sequence, int offset) {}

    public String toString() {}

    public String name() {}

    public String esc_name() {}

    public String jml_name() {}

    public String jml_name(boolean in_prestate) {}

    public String simplify_name() {}

    public String csharp_name() {}

    public void set_offset(int offset) {}
  }

  public static class VarPlusOffset extends Term {
    VarInfo var;
    int offset;

    public VarPlusOffset(VarInfo var) {}

    public VarPlusOffset(VarInfo var, int offset) {}

    public String name() {}

    public String esc_name() {}

    public String jml_name() {}

    public String jml_name(boolean in_prestate) {}

    public String simplify_name() {}
  }

  public static class QuantifyReturn {

    public VarInfo var;

    public /*@nullable@*/ Term index;

    public QuantifyReturn(VarInfo var) {
      this.var = var;
    }
  }

  public static QuantifyReturn[] quantify(VarInfo[] vars) {}

  public static class ESCQuantification {

    private Set flags;
    private VarInfo[] arr_vars;
    private String[] arr_vars_indexed;
    private String[] quants;
    private String quant;
    private Term[] indices;

    public ESCQuantification(Set flags, VarInfo[] vars) {}

    public String get_quantification() {}

    public String get_arr_vars_indexed(int num) {}
  }

  public static class SimplifyQuantification {

    Set flags;
    String quantification;
    String[] arr_vars_indexed;
    /*@nullable@*/ String[] indices;

    public SimplifyQuantification(Set flags, VarInfo[] vars) {}

    public String get_quantification() {}

    public String get_arr_vars_indexed(int num) {}

    public String get_index(int num) {}

    public String get_closer() {}
  }
}
