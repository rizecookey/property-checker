package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class Daikon {

  private Daikon() {}

  public static int dkconfig_progress_delay = 1000;
  public static final String release_version = "5.8.21";
  public static final String release_date = "May 14, 2024";
  public static final String release_string =
      "Daikon version "
          + release_version
          + ", released "
          + release_date
          + "; http://plse.cs.washington.edu/daikon.";
  public static boolean dkconfig_output_conditionals = true;
  public static boolean dkconfig_calc_possible_invs;
  public static int dkconfig_ppt_perc = 100;
  public static boolean dkconfig_print_sample_totals = false;
  public static final String lineSep = Global.lineSep;
  public static boolean dkconfig_quiet = false;
  public static final boolean check_program_types = true;
  public static final boolean invariants_check_canBeMissing = false;
  public static final boolean invariants_check_canBeMissing_arrayelt = true;
  public static final boolean disable_modbit_check_message = false;
  public static final boolean disable_modbit_check_error = false;
  public static boolean no_text_output = false;
  public static boolean show_progress = false;
  public static boolean use_equality_optimization = true;
  public static boolean dkconfig_undo_opts = false;
  public static boolean using_DaikonSimple = false;
  public static String dkconfig_guardNulls = "default";
  public static boolean use_dataflow_hierarchy = true;
  public static boolean suppress_redundant_invariants_with_simplify = false;
  //public static OutputFormat output_format = OutputFormat.DAIKON;
  public static boolean output_num_samples = false;
  public static boolean ignore_comparability = false;
  //public static /*@nullable@*/ Pattern ppt_regexp;
  //public static /*@nullable@*/ Pattern ppt_omit_regexp;
  //public static /*@nullable@*/ Pattern var_regexp;
  //public static /*@nullable@*/ Pattern var_omit_regexp;
  public static /*@nullable@*/ String ppt_max_name = null;
  public static /*@nullable@*/ File inv_file;
  private static boolean use_mem_monitor = false;
  public static boolean noversion_output = false;
  public static boolean isInferencing = false;
  public static boolean omit_from_output = false;
  public static boolean[] omit_types = new boolean[256];
  public static final String help_SWITCH = "help";
  public static final String no_text_output_SWITCH = "no_text_output";
  public static final String format_SWITCH = "format";
  public static final String show_progress_SWITCH = "show_progress";
  public static final String show_detail_progress_SWITCH = "show_detail_progress";
  public static final String no_show_progress_SWITCH = "no_show_progress";
  public static final String noversion_SWITCH = "noversion";
  public static final String output_num_samples_SWITCH = "output_num_samples";
  public static final String files_from_SWITCH = "files_from";
  public static final String omit_from_output_SWITCH = "omit_from_output";
  public static final String conf_limit_SWITCH = "conf_limit";
  public static final String list_type_SWITCH = "list_type";
  public static final String user_defined_invariant_SWITCH = "user-defined-invariant";
  public static final String disable_all_invariants_SWITCH = "disable-all-invariants";
  public static final String no_dataflow_hierarchy_SWITCH = "nohierarchy";
  public static final String suppress_redundant_SWITCH = "suppress_redundant";
  public static final String ppt_regexp_SWITCH = "ppt-select-pattern";
  public static final String ppt_omit_regexp_SWITCH = "ppt-omit-pattern";
  public static final String var_regexp_SWITCH = "var-select-pattern";
  public static final String var_omit_regexp_SWITCH = "var-omit-pattern";
  public static final String server_SWITCH = "server";
  public static final String config_SWITCH = "config";
  public static final String config_option_SWITCH = "config_option";
  public static final String debugAll_SWITCH = "debug";
  public static final String debug_SWITCH = "dbg";
  public static final String track_SWITCH = "track";
  public static final String disc_reason_SWITCH = "disc_reason";
  public static final String mem_stat_SWITCH = "mem_stat";
  public static final String wrap_xml_SWITCH = "wrap_xml";
  private static final String classGetNameRegex = "";
  //private static final Pattern classGetNamePattern;
  public static File server_dir = null;
  public static PptMap all_ppts;
  public static /*@nullable@*/ Invariant current_inv = null;
  public static ArrayList proto_invs = new ArrayList();
  //public static final Logger debugTrace = Logger.getLogger("daikon.Daikon");
  //public static final Logger debugProgress = Logger.getLogger("daikon.Progress");
  //public static final Logger debugEquality = Logger.getLogger("daikon.Equality");
  //public static final Logger debugInit = Logger.getLogger("daikon.init");
  //public static final Logger debugStats = Logger.getLogger("daikon.stats");
  static String usage;

  public abstract static class DaikonTerminationException extends RuntimeException {
    static final long serialVersionUID = 20180729L;
    protected DaikonTerminationException() {}
    protected DaikonTerminationException(String message) {}
    protected DaikonTerminationException(Throwable e) {}
    protected DaikonTerminationException(String message, Throwable e) {}
  }
  public static class NormalTermination extends DaikonTerminationException {
    static final long serialVersionUID = 20180729L;
    public NormalTermination(String message) {}
    public NormalTermination() {}
  }
  public static class BugInDaikon extends DaikonTerminationException {
    static final long serialVersionUID = 20180729L;
    public BugInDaikon(String message) {}
    public BugInDaikon(Throwable e) {}
    public BugInDaikon(String message, Throwable e) {}
  }
  public static class UserError extends DaikonTerminationException {
    static final long serialVersionUID = 20050923L;
    //public static String error_at_line_file(LineNumberReader reader, String filename, Throwable e) {}
    //public static String error_at_line_file(LineNumberReader reader, String filename, String msg) {}
    public UserError(Throwable e) {}
    public UserError(Throwable e, String msg) {}
    //public UserError(Throwable e, FileIO.ParseState state) {}
    //public UserError(Throwable e, LineNumberReader reader, String filename) {}
    //public UserError(Throwable e, String msg, LineNumberReader reader, String filename) {}
    public UserError() {}
    public UserError(String s) {}
    //public UserError(String msg, FileIO.ParseState state) {}
    //public UserError(String msg, LineNumberReader reader, String filename) {}
  }
  public static class ParseError extends Exception {
    static final long serialVersionUID = 20181021L;
    ParseError(String s) {}
  }

  public static void handleDaikonTerminationException(DaikonTerminationException e) {}

  public static void cleanup() {}

  public static class FileOptions {
    public Set decls;
    public Set dtrace;
    public Set spinfo;
    public Set map;
    public FileOptions(Set decls, Set dtrace, Set spinfo, Set map) {}
  }

  static FileOptions read_options(String[] args, String usage) {}

  //private static void setStaticField(Field field, Object value) throws IllegalAccessException {}

  //public static String getOptarg(Getopt g) {}

  private static List userDefinedInvariants;

  public static void setup_proto_invs() {}

  public static void createUpperPpts(PptMap all_ppts) {}

  public static void init_ppt(PptTopLevel ppt, PptMap all_ppts) {}

  public static void create_combined_exits(PptMap ppts) {}

  static List filter_invs(List invs) {}

  public static void setup_splitters(PptTopLevel ppt) {}

  public static int dkconfig_progress_display_width = 80;
  public static String progress = "";

  public static class FileIOProgress extends Thread {
    public FileIOProgress() {}
    public boolean shouldStop = false;
    public void run() {}
    public void clear() {}
    public void display() {}
    public void display(String message) {}
  }

  public static void ppt_stats(PptMap all_ppts) {}

  /* @EnsuresNonNull({
    "daikon.suppress.NIS.suppressor_map",
    "daikon.suppress.NIS.suppressor_map_suppression_count",
    "daikon.suppress.NIS.all_suppressions",
    "daikon.suppress.NIS.suppressor_proto_invs"
  })
  public static void setup_NISuppression() {
    NIS.init_ni_suppression();
  }*/

  public static void setupEquality(PptTopLevel ppt) {}

  public static void create_splitters(Set spinfo_files) throws IOException {}

  /* @RequiresNonNull({"daikon.suppress.NIS.all_suppressions", "daikon.suppress.NIS.suppressor_map"})
  public static void undoOpts(PptMap all_ppts) {

    // undo suppressions
    for (PptTopLevel ppt : all_ppts.ppt_all_iterable()) {
      NIS.create_suppressed_invs(ppt);
    }

    // undo equality sets
    for (PptTopLevel ppt : all_ppts.ppt_all_iterable()) {
      PptSliceEquality sliceEquality = ppt.equality_view;

      // some program points have no equality sets?
      if (sliceEquality == null) {
        // System.out.println(ppt.name);
        continue;
      }

      // get the new leaders
      List<Equality> allNewInvs = new ArrayList<>();

      for (Invariant eq_as_inv : sliceEquality.invs) {
        Equality eq = (Equality) eq_as_inv;
        VarInfo leader = eq.leader();
        List<VarInfo> vars = new ArrayList<>();

        for (VarInfo var : eq.getVars()) {
          if (!var.equals(leader)) {
            vars.add(var);
          }
        }

        if (vars.size() > 0) {

          // Create new equality sets for all of the non-equal vars
          List<Equality> newInvs = sliceEquality.createEqualityInvs(vars, eq);

          // Create new slices and invariants for each new leader
          // copyInvsFromLeader(sliceEquality, leader, vars);
          sliceEquality.copyInvsFromLeader(leader, vars);

          // Keep track of all of the new invariants created.
          // Add all of the new equality sets to our list
          allNewInvs.addAll(newInvs);
        }
      }

      sliceEquality.invs.addAll(allNewInvs);
    }
  }*/
}
