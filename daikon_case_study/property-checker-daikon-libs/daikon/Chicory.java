package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class Chicory {

public static boolean help = false;
public static boolean verbose = false;
public static boolean debug = false;
public static /*@nullable@*/ File dtrace_file = null;
public static /*@nullable@*/ File comparability_file = null;
public static File output_dir = new File(".");
public static /*@nullable@*/ File config_dir = null;
public static boolean daikon = false;
public static boolean daikon_online = false;
public static String daikon_args = "";
public static String heap_size = "3600m";
public static /*@nullable@*/ File premain = null;
public static List ppt_select_pattern = new ArrayList();
public static List ppt_omit_pattern = new ArrayList();
public static int sample_start = 0;
//public static /*@nullable@*/ Pattern boot_classes = null;
public static boolean instrument_clinit = false;
public static int nesting_depth = 2;
//public static /*@nullable@*/ Pattern omit_var = null;
public static boolean std_visibility = false;
public static /*@nullable@*/ File purity_file;
public static boolean debug_transform = false;
public static boolean debug_decl_print = false;
public static boolean debug_ppt_names = false;
private static int daikon_port = -1;
//public static /*@nullable@*/ StreamRedirectThread out_thread;
//public static /*@nullable@*/ StreamRedirectThread err_thread;
public static long start = 0;
//public static /*@nullable@*/ Process daikon_proc;
private static final String traceLimTermString = "DTRACELIMITTERMINATE";
private static final String traceLimString = "DTRACELIMIT";
public static final boolean checkStaticInit = true;
private static final boolean RemoteDebug = false;
private static boolean purityAnalysis = false;
//private static final SimpleLog basic = new SimpleLog(false);
public static final String synopsis = "daikon.Chicory [options] target [target-args]";

  //public static void check_args(Options options, String[] target_args) {}

  public static boolean doPurity() {}

  public static /*@nullable@*/ File get_purity_file() {}

  void start_target(String premain_args, String[] target_args) {}

  /* @ public normal_behavior
    @ ensures daikon_proc != null;
    @*/
  public void runDaikon() {}

  /* @ public normal_behavior
    @ requires daikon_proc != null;
    @*/
  private int waitForDaikon() {}

  //public int redirect_wait(Process p) {}

  public static String elapsed() {}

  public static long elapsed_msecs() {}

  public String args_to_string(List args) {}
}
