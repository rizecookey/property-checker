package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class VarInfo implements Cloneable {

  static final long serialVersionUID = 20060815L;

  public static boolean dkconfig_declared_type_comparability = true;
  public static boolean dkconfig_constant_fields_simplify = true;
  //public static final Logger debugMissing = Logger.getLogger("daikon.VarInfo.missing");
  public PptTopLevel ppt;

  public String name() {}

  public String str_name() {}

  public ProglangType type;
  public ProglangType file_rep_type;
  public ProglangType rep_type;
  public VarComparability comparability;
  public VarInfoAux aux;
  public int varinfo_index;
  public int value_index;
  public boolean is_static_constant;
  /*@nullable@*/ Object static_constant_value;
  //public /*@nullable@*/ Derivation derived;

  public enum RefType {
    POINTER,
    OFFSET
  };

  public enum LangFlags {
    PUBLIC,
    PRIVATE,
    PROTECTED,
    STATIC,
    FINAL,
    SYNCHRONIZED,
    VOLATILE,
    TRANSIENT,
    ANNOTATION,
    ENUM
  };

  public enum VarKind {
    FIELD,
    FUNCTION,
    ARRAY,
    VARIABLE,
    RETURN
  };

  public enum VarFlags {
    IS_PARAM,
    NO_DUPS,
    NOT_ORDERED,
    NO_SIZE,
    NOMOD,
    SYNTHETIC,
    CLASSNAME,
    TO_STRING,
    NON_NULL,
    IS_PROPERTY,
    IS_ENUM,
    IS_READONLY
  };

  public /*@nullable@*/ RefType ref_type;
  public VarKind var_kind;
  public Set var_flags;
  public Set lang_flags;
  //public VarDefinition vardef;
  public /*@nullable@*/ VarInfo enclosing_var;
  public int arr_dims;
  public /*@nullable@*/ List function_args = null;
  public List parents;
  public /*@nullable@*/ String relative_name = null;

  public boolean missingOutOfBounds() {}

  public boolean canBeMissing = false;
  public Equality equalitySet;
  private VarInfo sequenceSize;
  public /*@nullable@*/ VarInfo postState;

  public void checkRep() {}

  public void checkRepNoPpt() {}

  static boolean legalRepType(ProglangType rep_type) {}

  /*@ normal_behavior
    @ ensures !\result ==> constant_value != null;
    @*/
  static boolean legalConstant(/*@nullable@*/ Object constant_value) {}

  static boolean legalFileRepType(ProglangType file_rep_type) {}

  //public VarInfo(VarDefinition vardef) {}

  public void relate_var() {}

  public void setup_derived_function(String name, VarInfo[] bases) {}

  public void setup_derived_base(VarInfo base, /*@nullable@*/ VarInfo[] others) {}

  private VarInfo(VarInfoName name, ProglangType type, ProglangType file_rep_type, VarComparability comparability, boolean is_static_constant, /*@nullable@*/ Object static_constant_value, VarInfoAux aux) {}

  public VarInfo(String name, ProglangType type, ProglangType file_rep_type, VarComparability comparability, boolean is_static_constant, /*@nullable@*/ Object static_constant_value, VarInfoAux aux) {}

  private VarInfo(VarInfoName name, ProglangType type, ProglangType file_rep_type, VarComparability comparability, VarInfoAux aux) {}

  public VarInfo(String name, ProglangType type, ProglangType file_rep_type, VarComparability comparability, VarInfoAux aux) {}

  public VarInfo(VarInfo vi) {}

  public static VarInfo origVarInfo(VarInfo vi) {}

  public static VarInfo[] arrayclone_simple(VarInfo[] a_old) {}

  public void trimToSize() {}

  public String repr() {}

  // @EnsuresNonNullIf(result = true, expression = {"constantValue()", "static_constant_value"})
  /*@pure@*/ public boolean isStaticConstant() {}

  public Object constantValue() {}

  /* @ public normal_behavior
    @ ensures \result ==> postState != null;
    @ assignable \nothing;
    @*/
  public boolean isPrestate() {}

  /*@pure@*/ public boolean isPrestateDerived() {}

  /* @ public normal_behavior
    @ ensures \result ==> derived != null;
    @*/
  public boolean isDerived() {}

  public int derivedDepth() {}

  public List derivees() {}

  public List get_all_constituent_vars() {}

  public List get_all_simple_names() {}

  /*@pure@*/ public boolean isClosure() {}

  public /*@nullable@*/ VarInfo derivedParamCached = null;

  public /*@nullable@*/ Boolean isDerivedParamCached = null;

  // @EnsuresNonNullIf(result = true, expression = "getDerivedParam()")
  /*@pure@*/ public boolean isDerivedParam() {}

  /*@pure@*/ public /*@nullable@*/ VarInfo getDerivedParam() {}

  /*@pure@*/ public boolean isDerivedParamAndUninteresting() {}

  /*@pure@*/ public int getModified(ValueTuple vt) {}

  /*@pure@*/ public boolean isUnmodified(ValueTuple vt) {}

  /*@pure@*/ public boolean isModified(ValueTuple vt) {}

  /*@pure@*/ public boolean isMissingNonsensical(ValueTuple vt) {}

  /*@pure@*/ public boolean isMissingFlow(ValueTuple vt) {}

  /*@pure@*/ public boolean isMissing(ValueTuple vt) {}

  public Object getValue(ValueTuple vt) {}

  public /*@nullable@*/ Object getValueOrNull(ValueTuple vt) {}

  public int getIndexValue(ValueTuple vt) {}

  public long getIntValue(ValueTuple vt) {}

  public long[] getIntArrayValue(ValueTuple vt) {}

  public double getDoubleValue(ValueTuple vt) {}

  public double[] getDoubleArrayValue(ValueTuple vt) {}

  public String getStringValue(ValueTuple vt) {}

  public String[] getStringArrayValue(ValueTuple vt) {}

  /*@pure@*/ public boolean isCanonical() {}

  /*@pure@*/ public VarInfo canonicalRep() {}

  /*@pure@*/ public boolean is_reference() {}

  public /*@nullable@*/ VarInfo isDerivedSequenceMember() {}

  /*@pure@*/ public boolean isDerivedSequenceMinMaxSum() {}

  public /*@nullable@*/ VarInfo isDerivedSubSequenceOf() {}

  public /*@nullable@*/ VarInfo sequenceSize() {}

  /*@pure@*/ public boolean isIndex() {}

  /*@pure@*/ public boolean is_array() {}

  /*@pure@*/ public boolean isValidEscExpression() {}

  /*@pure@*/ public boolean isPointer() {}

  public String simplifyFixup(String str) {}

  public String simplifyFixedupName() {}

  public static boolean compare_vars(VarInfo vari, int vari_shift, VarInfo varj, int varj_shift, boolean test_lessequal) {}

  public /*@nullable@*/ VarInfoName preStateEquivalent() {}

  public /*@nullable@*/ VarInfoName otherStateEquivalent(boolean post) {}

  /*@pure@*/ public boolean isEqualTo(VarInfo other) {}

  public static boolean assertionsEnabled() {}

  public void simplify_expression() {}

  public boolean compatible(VarInfo var2) {}

  public boolean eltsCompatible(VarInfo sclvar) {}

  public boolean comparableByType(VarInfo var2) {}

  public boolean comparableNWay(VarInfo var2) {}

  public boolean indexCompatible(VarInfo sclvar) {}

  public /*@nullable@*/ Invariant createGuardingPredicate(boolean install) {}

  static Set addVarMessages;

  public List getGuardingList() {}

  public List get_all_enclosing_vars() {}

  public static final class IndexComparator implements Serializable {

    static final long serialVersionUID = 20050923L;

    private IndexComparator() {}

    /*@pure@*/
    public int compare(VarInfo vi1, VarInfo vi2) {}

    public static IndexComparator getInstance() {}

    public static final IndexComparator theInstance = new IndexComparator();
  }

  public /*@nullable@*/ PptTopLevel find_object_ppt(PptMap all_ppts) {}

  public static class Pair {

    public VarInfo v1;
    public VarInfo v2;
    public int samples;

    public Pair(VarInfo v1, VarInfo v2, int samples) {}
  }

  public ValueSet get_value_set() {}

  public String get_value_info() {}

  public int get_equalitySet_size() {}

  public Set get_equalitySet_vars() {}

  public VarInfo get_equalitySet_leader() {}

  private static Set out_strings;

  static void debug_print_once(String format, /*@nullable@*/ Object[] args) {}

  /*@pure@*/ public boolean isParam() {}

  public void set_is_param() {}

  public void set_is_param(boolean set) {}

  public String apply_subscript(String subscript) {}

  public static String apply_subscript(String sequence, String subscript) {}

  public VarInfo get_array_var() {}

  public VarInfo get_base_array() {}

  /*@pure@*/ public /*@nullable@*/ VarInfo get_base_array_hashcode() {}

  public Quantify.Term get_lower_bound() {}

  public Quantify.Term get_upper_bound() {}

  public Quantify.Term get_length() {}

  public void update_after_moving_to_new_ppt() {}

  public VarInfoName get_VarInfoName() {}

  public static String fix_csharp_type_name(String type) {}

  public String csharp_collection_string() {}

  public String[] csharp_array_split() {}

  //public String name_using(OutputFormat format) {}

  public String csharp_name() {}

  public String csharp_name(/*@nullable@*/ String index) {}

  public String java_name() {}

  public String dbc_name() {}

  public String esc_name() {}

  public String esc_name(/*@nullable@*/ String index) {}

  public String jml_name() {}

  public String jml_name(/*@nullable@*/ String index) {}

  public String simplify_name() {}

  public String simplify_name(/*@nullable@*/ String index) {}

  public String prestate_name() {}

  public /*@nullable@*/ String get_simplify_size_name() {}

  public boolean includes_simple_name(String varname) {}

  public static String[] esc_quantify(VarInfo[] vars) {}

  public static String[] esc_quantify(boolean elementwise, VarInfo[] vars) {}

  public String /*@nullable@*/ [] simplifyNameAndBounds() {}

  public String /*@nullable@*/ [] get_simplify_slice_bounds() {}

  public String get_simplify_selectNth(String simplify_index_name, boolean free, int index_off) {}

  public String get_simplify_selectNth_lower(int index_off) {}

  public static String get_simplify_free_index(VarInfo[] vars) {
  }

  public static String[] get_simplify_free_indices(VarInfo[] vars) {}

  public static String[] simplify_quantify(Set flags, VarInfo[] vars) {}

  public static String[] simplify_quantify(VarInfo[] vars) {}

  public int complexity() {}

  /*@pure@*/ public boolean is_assignable_var() {}

  /*@pure@*/ public boolean is_typeof() {}

  public boolean has_typeof() {}

  /*@pure@*/ public boolean is_this() {}

  /*@pure@*/ public boolean isThis() {}

  /*@pure@*/ public boolean is_size() {}

  /*@pure@*/ public boolean is_field() {}

  /*@pure@*/ public boolean is_add() {}

  public int get_add_amount() {}

  /*@pure@*/ public boolean is_direct_array() {}

  /*@pure@*/ public boolean is_direct_non_slice_array() {}

  public boolean has_same_parent(VarInfo other) {}

  public /*@nullable@*/ VarInfo get_enclosing_var() {}

  public String replace_this(VarInfo arg) {}

  public static VarInfo make_subsequence(VarInfo seq, /*@nullable@*/ VarInfo begin, int begin_shift, /*@nullable@*/ VarInfo end, int end_shift) {}

  public static VarInfo make_subscript(VarInfo seq, /*@nullable@*/ VarInfo index, int index_shift) {}

  public static VarInfo make_function(String function_name, VarInfo[] vars) {}

  public static VarInfo make_scalar_seq_func(String func_name, /*@nullable@*/ ProglangType type, VarInfo seq, int shift) {}

  public static VarInfo make_scalar_str_func(String func_name, ProglangType type, VarInfo str) {}

  /*@pure@*/ public boolean is_prestate_version(VarInfo vi) {}

  /*@pure@*/ public boolean isArray() {}

  /*@pure@*/ public boolean isSlice() {}

  public static String old_var_names(String name) {}

  public String old_var_name() {}

  public void var_check() {}
}
