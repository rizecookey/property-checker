package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class DynComp {

  public static boolean help = false;
  public static boolean verbose = false;
  public static boolean dump = false;
  public static boolean debug = false;
  public static File debug_dir = new File("debug");
  public static File output_dir = new File(".");
  public static /*@nullable@*/ String decl_file = null;
  public static /*@nullable@*/ File comparability_file = null;
  public static /*@nullable@*/ File trace_file = null;
  public static int trace_line_depth = 1;
  public static boolean abridged_vars = false;
  public static List ppt_select_pattern = new ArrayList();
  public static List ppt_omit_pattern = new ArrayList();
  public static /*@nullable@*/ File rt_file = null;
  public static boolean std_visibility = false;
  public static int nesting_depth = 2;
  public static /*@nullable@*/ File premain = null;
  public static String daikonPath = "";
  static /*@nullable@*/ String cp = null;
  static /*@nullable@*/ String java_lib_classpath = null;
  static /*@nullable@*/ String daikon_dir = null;
  public static boolean debug_transform = false;
  public static boolean debug_decl_print = false;
  public static boolean no_jdk = false;
  public static long start = 0;
  //private static final SimpleLog basic = new SimpleLog(false);
  public static final String synopsis = "daikon.DynComp [options] target [target-args]";

  //public static void check_args(Options options, String[] targetArgs) {}

  /*@ normal_behavior
    @ ensures cp != null;
    @*/
  void start_target(String premain_args, String[] targetArgs) {}

  //public int redirect_wait(Process p) {}

  public static String elapsed() {}

  public static long elapsedMsecs() {}

  public String argsToString(List args) {}

  boolean isDaikonOnPath(String path) {}

  /*@ normal_behavior
    @ requires cp != null;
    @*/
  public /*@nullable@*/ File locateFile(String fileName) {}

  /*@ normal_behavior
    @ requires cp != null;
    @*/
  public /*@nullable@*/ File findOnClasspath(String fileName) {}
}
