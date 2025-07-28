package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class FileIO {

  private FileIO() {}

  static final String declaration_header = "DECLARE";
  public static final String ppt_tag_separator = ":::";
  public static final String enter_suffix = "ENTER";
  public static final String enter_tag = ppt_tag_separator + enter_suffix;
  public static final String exit_suffix = "EXIT";
  public static final String exit_tag = ppt_tag_separator + exit_suffix;
  public static final String throws_suffix = "THROWS";
  public static final String throws_tag = ppt_tag_separator + throws_suffix;
  public static final String object_suffix = "OBJECT";
  public static final String object_tag = ppt_tag_separator + object_suffix;
  public static final String class_static_suffix = "CLASS";
  public static final String class_static_tag = ppt_tag_separator + class_static_suffix;
  public static final String global_suffix = "GLOBAL";
  private static final String lineSep = Global.lineSep;
  public static boolean dkconfig_ignore_missing_enter = false;
  public static boolean dkconfig_add_changed = true;
  public static int dkconfig_max_line_number = 0;
  public static boolean dkconfig_count_lines = true;
  public static boolean dkconfig_read_samples_only = false;
  public static boolean dkconfig_unmatched_procedure_entries_quiet = false;
  public static boolean dkconfig_verbose_unmatched_procedure_entries = false;
  public static boolean dkconfig_continue_after_file_exception = false;
  public static long dkconfig_dtrace_line_count = 0;
  public static /*@nullable@*/ Boolean new_decl_format = null;

  public static void resetNewDeclFormat() {}

  public static boolean dkconfig_rm_stack_dups = false;
  static Map ppt_to_value_reps;
  private static boolean to_write_nonce = false;
  private static final String NONCE_HEADER = "this_invocation_nonce";
  private static String nonce_value = "no nonce (yet)";
  public static int omitted_declarations = 0;
  public static boolean debug_missing = false;
  //public static final Logger debugRead = Logger.getLogger("daikon.FileIO.read");
  //public static final Logger debugPrint = Logger.getLogger("daikon.FileIO.printDtrace");
  //public static final Logger debugVars = Logger.getLogger("daikon.FileIO.vars");

  public static final class ParentRelation implements java.io.Serializable {
    static final long serialVersionUID = 20060622L;
    public PptRelation.PptRelationType rel_type;
    public String parent_ppt_name;
    public int id;

    public ParentRelation(PptRelation.PptRelationType rel_type, String parent_ppt_name, int id) {}
  }

  /*@ public normal_behavior
    @ ensures \result ==> s != null;
    @ assignable \nothing;
    @*/
  public static final boolean isComment(/*@nullable@*/ String s) {}

  // @EnsuresNonNullIf(result = true, expression = "#1.readLine()")
  // public static final boolean nextLineIsComment(BufferedReader reader) {}

  public static PptMap read_declaration_files(Collection files) throws IOException {}

  public static void read_declaration_file(File filename, PptMap all_ppts) throws IOException {}

  static final class Invocation {

    PptTopLevel ppt;

    /*@nullable@*/ Object[] vals;
    int[] mods;
    static Object canonical_hashcode = new Object();

    Invocation(PptTopLevel ppt, /*@nullable@*/ Object[] vals, int[] mods) {}

    String format() {}

    String format(boolean show_values) {}

    public Invocation canonicalize() {}
  }

  static Map call_hashmap;
  //static Deque call_stack = new ArrayDeque();

  public static void read_data_trace_files(Collection files, PptMap all_ppts) throws IOException {}

  public static class Processor {

    public void process_sample(PptMap all_ppts, PptTopLevel ppt, ValueTuple vt, /*@nullable@*/ Integer nonce) {}

    public void process_decl(PptMap all_ppts, PptTopLevel ppt) {}

    public void process_decl_version(String format) {}

    public void process_comparability(String comparability) {}

    public void process_list_implementors(String implementors) {}

    public void process_input_language(String language) {}

    public void process_null() {}

    public void process_comment(String comment) {}

    public void process_eof() {}

    public void process_truncated() {}

    public void process_error() {}
  }

  public static int samples_processed = 0;

  public enum RecordType {
    SAMPLE,
    DECL,
    DECL_VERSION,
    COMPARABILITY,
    LIST_IMPLEMENTORS,
    INPUT_LANGUAGE,
    NULL,
    COMMENT,
    EOF,
    TRUNCATED,
    ERROR
  };

  public static class ParseState {

    public String filename;
    public boolean is_decl_file;
    public boolean ppts_may_be_new;
    public PptMap all_ppts;
    //public final LineNumberReader reader;
    public long total_lines;
    public int varcomp_format;
    public RecordType rtype;
    public /*@nullable@*/ PptTopLevel ppt;
    public /*@nullable@*/ Integer nonce;
    public /*@nullable@*/ ValueTuple vt;
    public /*@nullable@*/ Object payload; // used when status=COMMENT

    public ParseState(String raw_filename, boolean decl_file_p, boolean ppts_may_be_new, PptMap ppts) throws IOException {}

    public void close() {}

    public int get_linenum() {}

    public String reading_message() {}

    public String line_file_message() {}
  }

  public static int get_linenum() {}

  public static /*@nullable@*/ ParseState data_trace_state = null;

  public static void read_data_trace_file(String filename, PptMap all_ppts) throws IOException {}

  public static void read_data_trace_file(String filename, PptMap all_ppts, Processor processor, boolean is_decl_file, boolean ppts_may_be_new) throws IOException {}

  public static void read_data_trace_record_setstate(ParseState state) throws IOException {}

  /*@ public normal_behavior
    @ requires FileIO.data_trace_state != null;
    @*/
  public static void read_data_trace_record(ParseState state) throws IOException {}

  /*@ public normal_behavior
    @ requires FileIO.data_trace_state != null;
    @*/
  static boolean has_unmatched_procedure_entry(PptTopLevel ppt) {}

  public static void process_unmatched_procedure_entries() {}

  static void print_invocations_verbose(Collection invocations) {}

  static void print_invocations_grouped(Collection invocations) {}

  /*@ public normal_behavior
    @ requires FileIO.data_trace_state != null;
    @*/
  public static boolean compute_orig_variables(PptTopLevel ppt, /*@nullable@*/ Object[] vals, int[] mods, /*@nullable@*/ Integer nonce) {}

  public static void compute_derived_variables(PptTopLevel ppt, /*@nullable@*/ Object[] vals, int[] mods) {}

  static final class SerialFormat implements Serializable {

    static final long serialVersionUID = 20060905L;

  /* @ public normal_behavior
    @ requires FileIO.data_trace_state != null;
    @*/
    //public SerialFormat(PptMap map, Configuration config) {}

    public PptMap map;
    //public Configuration config;
    public boolean new_decl_format = false;
  }

  public static void write_serialized_pptmap(PptMap map, File file) throws IOException {}

  /*@ public normal_behavior
    @ ensures FileIO.new_decl_format != null;
    @*/
  public static PptMap read_serialized_pptmap(File file, boolean use_saved_config) throws IOException {}

  public static boolean ppt_included(String ppt_name) {}

  public static boolean var_included(String var_name) {}

  static void check_decl_match(ParseState state, PptTopLevel existing_ppt, VarInfo[] vi_array) {}

  //public static String need(ParseState state, Scanner scanner, String description) {}

  //public static void need_eol(ParseState state, Scanner scanner) {}

  //public static Enum parse_enum_val(ParseState state, Scanner scanner, Class<E> enum_class, String descr) {}

  public static String user_mod_ppt_name(String ppt_name) {}
}
