package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class PrintInvariants {

  private PrintInvariants() {}

  public static void resetPrestateExpressions() {}

  public static String addPrestateExpression(String expr) {}
  public static boolean dkconfig_replace_prestate = true;
  public static boolean dkconfig_print_inv_class = false;
  public static boolean dkconfig_print_all = false;
  public static boolean dkconfig_true_inv_cnt = false;
  public static boolean dkconfig_remove_post_vars = false;
  public static boolean dkconfig_old_array_names = true;
  public static boolean dkconfig_static_const_infer = false;
  public static boolean dkconfig_print_implementer_entry_ppts = true;
  //public static final Logger debug = Logger.getLogger("daikon.PrintInvariants");
  //public static final Logger debugRepr = Logger.getLogger("daikon.PrintInvariants.repr");
  //public static final Logger debugPrint = Logger.getLogger("daikon.print");
  //public static final Logger debugPrintModified = Logger.getLogger("daikon.print.modified");
  //public static final Logger debugPrintEquality = Logger.getLogger("daikon.print.equality");
  //public static final Logger debugFiltering = Logger.getLogger("daikon.filtering");
  //public static final Logger debugBound = Logger.getLogger("daikon.bound");
  public static boolean print_discarded_invariants = false;
  public static boolean wrap_xml = false;

  public static void print_reasons(PptMap ppts) {}

  public static void validateGuardNulls() {}

  public static void discReasonSetup(String arg) {}

  // @RequiresNonNull("FileIO.new_decl_format")
  public static void print_invariants(PptMap all_ppts) {}

  // @RequiresNonNull("FileIO.new_decl_format")
  //public static void print_invariants_maybe(PptTopLevel ppt, PrintWriter out, PptMap all_ppts) {}

  // @RequiresNonNull("FileIO.new_decl_format")
  //public static void print_sample_data(PptTopLevel ppt, PrintWriter out) {}

  //public static void print_modified_vars(PptTopLevel ppt, PrintWriter out) {}

  public static void count_global_stats(PptTopLevel ppt) {}

  // @RequiresNonNull("FileIO.new_decl_format")
  //public static void print_invariant(Invariant inv, PrintWriter out, int invCounter, PptTopLevel ppt) {}

  public static String parse_csharp_invariant_variable(VarInfo varInfo, boolean sort) {}

  public static void get_csharp_invariant_variables(VarInfo[] vars, Set variables, boolean sort) {}

  public static void get_csharp_invariant_variables(Invariant invariant, Set variables, boolean group) {}

  public static String get_csharp_inv_type(Invariant invariant) {}

  public static List sort_invariant_list(List invs) {}

  /** Print invariants for a single program point, once we know that this ppt is worth printing. */
  // @RequiresNonNull("FileIO.new_decl_format")
  //public static void print_invariants(PptTopLevel ppt, PrintWriter out, PptMap ppt_map) {}

  public static void print_all_ternary_invs(PptMap all_ppts) {}

  public static void print_all_invs(PptTopLevel ppt, VarInfo vi, String indent) {}

  public static void print_all_invs(PptTopLevel ppt, VarInfo v1, VarInfo v2, String indent) {}

  public static void print_all_invs(/*@nullable@*/ PptSlice slice, String indent) {}

  //public static void print_filter_stats(Logger log, PptTopLevel ppt, PptMap ppt_map) {}

  // @RequiresNonNull({"daikon.suppress.NIS.all_suppressions", "daikon.suppress.NIS.suppressor_map"})
  public static void print_true_inv_cnt(PptMap ppts) {}
}
