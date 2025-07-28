package daikon;

import java.io.*;
import java.util.*;
import java.util.logging.*;
import daikon.inv.*;

public class PptTopLevel extends Ppt {

  static final long serialVersionUID = 20071129L;
  public static boolean dkconfig_pairwise_implications = false;
  public static boolean dkconfig_remove_merged_invs = false;
  public static boolean first_pass_with_sample = true;

  public enum PptFlags {
    STATIC,
    ENTER,
    EXIT,
    PRIVATE,
    RETURN
  };

  public Set flags;

  public enum PptType {
    POINT,
    CLASS,
    OBJECT,
    ENTER,
    EXIT,
    SUBEXIT
  }

  public PptType type;

  public int instantiated_inv_cnt = 0;
  public int instantiated_slice_cnt = 0;
  public static final Logger debug = Logger.getLogger("daikon.PptTopLevel");
  public static final Logger debugInstantiate = Logger.getLogger("daikon.PptTopLevel.instantiate");
  public static final Logger debugTimeMerge = Logger.getLogger("daikon.PptTopLevel.time_merge");
  public static final Logger debugEqualTo = Logger.getLogger("daikon.PptTopLevel.equal");
  //public static final Logger debugAddImplications =
  public static final Logger debugConditional = Logger.getLogger("daikon.PptTopLevel.conditional");
  public static final Logger debugFlow = Logger.getLogger("daikon.flow.flow");
  public static final Logger debugMerge = Logger.getLogger("daikon.PptTopLevel.merge");
  public static final Logger debugNISStats = Logger.getLogger("daikon.PptTopLevel.NISStats");
  public final String name;
  public final PptName ppt_name;

  /*@pure@*/ /*@helper@*/ public String name() {}

  private static int[] permute_swap = new int[] {1, 0};

  public /*@nullable*/ DynamicConstants constants = null;

  public int num_declvars;
  public int num_tracevars;
  public int num_orig_vars;
  public int num_static_constant_vars;
  ModBitTracker mbtracker;
  ValueSet[] value_sets;
  public /*@nullable@*/ ArrayList splitters = null;

  public class CondIterator implements java.util.Iterator {

    int splitter_index = 0;
    int ppts_index = 0;
  }

  public CondIterator cond_iterator() {}

  public Iterable cond_iterable() {}

  /*@ public normal_behavior
    @ ensures \result ==> splitters != null;
    @*/
  public boolean has_splitters() {}

  public List children = new ArrayList();
  public List parents = new ArrayList();
  public List parent_relations;
  public boolean invariants_merged = false;
  public boolean in_merge = false;
  public boolean invariants_removed = false;
  public PptSlice0 joiner_view = new PptSlice0(this);
  public /*@nullable@*/ PptSliceEquality equality_view;
  public Set redundant_invs;
  public Set redundant_invs_equality;
  public PptTopLevel(String name, PptType type, List parents, Set flags, VarInfo[] var_infos) {}

  public PptTopLevel(String name, VarInfo[] var_infos) {}

  public int num_array_vars() {}

  public Iterator var_info_iterator() {}

  public void trimToSize() {}

  public int num_samples() {}

  public int num_samples(VarInfo vi1) {}

  public int num_samples(VarInfo vi1, VarInfo vi2) {}

  public int num_samples(VarInfo vi1, VarInfo vi2, VarInfo vi3) {}

  public int num_values(VarInfo vi1) {}

  public int num_values(VarInfo vi1, VarInfo vi2) {}

  public int num_values(VarInfo vi1, VarInfo vi2, VarInfo vi3) {}

  Collection viewsAsCollection() {}

  public int numViews() {}

  void addVarInfos(VarInfo[] vis) {}

  public static boolean worthDerivingFrom(VarInfo vi) {}

  public List inv_add(List inv_list, ValueTuple vt, int count) {}

  public void get_missingOutOfBounds(PptTopLevel ppt, ValueTuple vt) {}

  /*@ public normal_behavior
    @ ensures \result ==> constants != null;
    @ assignable \nothing;
    @*/
  public boolean is_constant(VarInfo v) {}

  /*@ public normal_behavior
    @ ensures \result ==> constants != null;
    @ assignable \nothing;
    @*/
  public boolean is_prev_constant(VarInfo v) {}

  /*@ public normal_behavior
    @ ensures \result ==> constants != null;
    @ assignable \nothing;
    @*/
  public boolean is_missing(VarInfo v) {}

  /*@ public normal_behavior
    @ ensures \result ==> constants != null;
    @ assignable \nothing;
    @*/
  public boolean is_prev_missing(VarInfo v) {}

  public int invariant_cnt() {}

  public int const_slice_cnt() {}

  public int const_inv_cnt() {}

  static class Cnt {
    public int cnt = 0;
  }

  //public void debug_invs(Logger log) {}

  //public void debug_unary_info(Logger log) {}

  public Map invariant_cnt_by_class() {}

  public int slice_cnt() {}

  public void create_derived_variables() {}

  public void addViews(List slices_vector) {}

  public void addSlice(PptSlice slice) {}

  public void removeSlice(PptSlice slice) {}

  public void remove_invs(List rm_list) {}

  public /*@nullable@*/ PptSlice1 findSlice(VarInfo v) {}

  public /*@nullable@*/ PptSlice2 findSlice(VarInfo v1, VarInfo v2) {}

  public /*@nullable@*/ PptSlice2 findSlice_unordered(VarInfo v1, VarInfo v2) {}

  public /*@nullable@*/ PptSlice3 findSlice(VarInfo v1, VarInfo v2, VarInfo v3) {}

  public /*@nullable@*/ PptSlice3 findSlice_unordered(VarInfo v1, VarInfo v2, VarInfo v3) {}

  public /*@nullable@*/ PptSlice findSlice_unordered(VarInfo[] vis) {}

  public /*@nullable@*/ PptSlice findSlice(VarInfo[] vis) {}

  public /*@nullable@*/ Invariant find_inv_by_class(VarInfo[] vis, Class cls) {}

  public /*@nullable@*/ List find_assignment_inv(VarInfo v) {}

  /*@pure@*/ public PptSlice get_temp_slice(VarInfo v) {}

  /*@pure@*/ public PptSlice get_temp_slice(VarInfo v1, VarInfo v2) {}

  public /*@nullable@*/ DiscardInfo check_implied(Invariant imp_inv, VarInfo v, Invariant proto) {}

  public /*@nullable@*/ DiscardInfo check_implied_canonical(Invariant imp_inv, VarInfo v, Invariant proto) {}

  public /*@nullable@*/ DiscardInfo check_implied(Invariant imp_inv, VarInfo v1, VarInfo v2, Invariant proto) {}

  public boolean check_implied(DiscardInfo di, VarInfo v1, VarInfo v2, Invariant proto) {}

  public /*@nullable@*/ DiscardInfo check_implied_canonical(Invariant imp_inv, VarInfo v1, VarInfo v2, Invariant proto) {}

  public boolean check_implied_canonical(DiscardInfo di, VarInfo v1, VarInfo v2, Invariant proto) {}

  /*@pure@*/ public boolean is_subset(VarInfo v1, VarInfo v2) {}

  /*@pure@*/ public boolean is_nonzero(VarInfo v) {}

  /*@pure@*/ public boolean is_equal(VarInfo v1, VarInfo v2) {}

  /*@pure@*/ public boolean is_less_equal(VarInfo v1, int v1_shift, VarInfo v2, int v2_shift) {}

  /*@pure@*/ public boolean is_subsequence(VarInfo v1, VarInfo v2) {}

  /*@pure@*/ public boolean is_empty(VarInfo varr) {}

  public void instantiate_views_and_invariants() {}

  /*@pure@*/ public boolean is_slice_ok(VarInfo[] vis, int arity) {}

  /*@pure@*/ public boolean is_slice_ok(VarInfo var1) {}

  /*@pure@*/ public boolean is_slice_ok(VarInfo var1, VarInfo var2) {}

  /*@pure@*/ public boolean is_slice_ok(VarInfo v1, VarInfo v2, VarInfo v3) {}

  public boolean vis_order_ok(VarInfo[] vis) {}

  public PptSlice get_or_instantiate_slice(VarInfo[] vis) {}

  public PptSlice get_or_instantiate_slice(VarInfo vi) {}

  public PptSlice get_or_instantiate_slice(VarInfo v1, VarInfo v2) {}

  public PptSlice get_or_instantiate_slice(VarInfo v1, VarInfo v2, VarInfo v3) {}

  //public void addConditions(Splitter[] splits) {}

  ///*@pure@*/ public static /*@nullable@*/ LemmaStack getProverStack() {}

  public void addImplications() {}

  public void postProcessEquality() {}

  public static interface SimplifyInclusionTester {
    public boolean include(Invariant inv);
  }

  public void mark_implied_via_simplify(PptMap all_ppts) {}

  public static boolean format_simplify_problem(String s) {}

  /*@pure@*/ public Set getParamVars() {}

  public List getInvariants() {}

  public List invariants_vector() {}

  public Iterator views_iterator() {}

  public Iterable views_iterable() {}

  public Iterator invariants_iterator() {}

  public static final class ViewsIteratorIterator implements Iterator {

    Iterator vitor;
    /*@nullable@*/ Iterator implication_iterator;

    public ViewsIteratorIterator(PptTopLevel ppt) {}
  }

  public void simplify_variable_names() {}

  public static final Comparator icfp = new Invariant.InvariantComparatorForPrinting();

  static Comparator arityVarnameComparator = new PptSlice.ArityVarnameComparator();

  public void processOmissions(boolean[] omitTypes) {}

  public void repCheck() {}

  public String debugSlices() {}

  public void debug_print_tree(Logger l, int indent, /*@nullable@*/ PptRelation parent_rel) {}

  public String equality_sets_txt() {}

  public boolean has_parent(VarInfo v) {}

  public void mergeInvs() {}

  /*@ public normal_behavior
    @ requires equality_view != null;
    @*/
  public void merge_invs_multiple_children() {}

  public void merge_invs_one_child() {}

  public VarInfo /*@nullable@*/ [] parent_vis(PptRelation rel, PptSlice slice) {}

  public void merge_conditionals() {}

  public void clean_for_merge() {}

  public void remove_equality_invariants() {}

  public void remove_implications() {}

  public void remove_child_invs(PptRelation rel) {}

  public static int[] build_permute(VarInfo[] vis1, VarInfo[] vis2) {}

  //public void debug_print_slice_info(Logger log, String descr, List<PptSlice> slices) {}

  public PptSlice create_equality_inv(VarInfo v1, VarInfo v2, int samples) {}

  public static class Stats {

    public int sample_cnt = 0;
    public int set_cnt = 0;
    public int var_cnt = 0;
    public int time = 0;
    public long memory = 0;
    public int inv_cnt = 0;
    public int slice_cnt = 0;
    public int instantiated_inv_cnt = 0;
    public int instantiated_slice_cnt = 0;
    public /*@nullable@*/ PptTopLevel ppt;
    int const_slice_cnt = 0;
    int const_inv_cnt = 0;
    int constant_leader_cnt = 0;
    public static boolean cnt_inv_classes = false;
    /*@nullable@*/ Map inv_map = null;
    public static boolean show_invs = false;
    public static boolean show_tern_slices = false;

    /*@ normal_behavior
      @ ensures ppt != null;
      @*/
    void set(PptTopLevel ppt, int time, int memory) {}

    //static void dump_header(Logger log) {}

    /* @ normal_behavior
      @ ensures ppt != null;
      @*/
    //void dump(Logger log) {}
  }

  //public static void print_equality_stats(Logger log, PptMap all_ppts) {}

  void set_sample_number(int val) {}

  public void incSampleNumber() {}

  /*@pure@*/ public boolean is_exit() {}

  /*@pure@*/ public boolean is_enter() {}

  /*@pure@*/ public boolean is_combined_exit() {}

  /*@pure@*/ public boolean is_subexit() {}

  /*@pure@*/ public boolean is_object() {}

  /*@ public normal_behavior
    @ ensures \result ==> type != null;
    @ assignable \nothing;
    @*/
  public boolean is_class() {}

  public String var_names() {}
}
