package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class Debug {

  //public static final Logger debugTrack = Logger.getLogger("daikon.Debug");
  public static String[] debugTrackClass;

  public static /*@nullable@*/ String function_binary_method = null;

  public static String[] debugTrackPpt = {};

  public static String[][] debugTrackVars = {};
  public boolean cache_match = true;
  public /*@nullable@*/ Class cache_class;
  public /*@nullable@*/ Ppt cache_ppt;
  public VarInfo[] cache_vis;

  public Debug(Class c, Ppt ppt, VarInfo[] vis) {}

  public static /*@nullable@*/ Debug newDebug(Class c, Ppt ppt, VarInfo[] vis) {}

  public Debug(Class c, Ppt ppt, List vis) {}

  public /*@nullable@*/ VarInfo visTracked(List vis) {}
  private static /*@nullable@*/ String[] ourvars = new String[3];
  private static final VarInfo[] vis1 = new VarInfo[1];
  private static final VarInfo[] vis2 = new VarInfo[2];
  private static final VarInfo[] vis3 = new VarInfo[3];

  public static VarInfo[] vis(VarInfo v1) {}

  public static VarInfo[] vis(VarInfo v1, VarInfo v2) {}

  public static VarInfo[] vis(VarInfo v1, VarInfo v2, VarInfo v3) {}

  void /*@helper@*/ set(/*@nullable@*/ Class c, /*@nullable@*/ Ppt ppt, VarInfo[] vis) {}

  public static boolean dkconfig_internal_check = false;
  public static boolean dkconfig_show_stack_trace = false;
  public static boolean dkconfig_showTraceback = false;
  public static boolean dkconfig_logDetail = false;

  public static final boolean logDetail() {}

  public static final boolean logOn() {}

  //public void log(Logger debug, String msg) {}

  //public static void log(Logger debug, Class inv_class, /*@nullable@*/ Ppt ppt, String msg) {}

  //public static void log(Logger debug, /*@nullable@*/ Class inv_class, /*@nullable@*/ Ppt ppt, VarInfo[] vis, String msg) {}

  public boolean log(String msg) {}

  public static boolean log(Class inv_class, Ppt ppt, String msg) {}

  public static boolean log(/*@nullable@*/ Class inv_class, /*@nullable@*/ Ppt ppt, VarInfo[] vis, String msg) {}

  public static boolean class_match(/*@nullable@*/ Class inv_class) {}

  public static boolean ppt_match(/*@nullable@*/ Ppt ppt) {}

  public static boolean var_match(VarInfo[] vis) {}

  private static boolean strContainsElem(String str, String[] arr) {}

  public static void check(PptMap all_ppts, String msg) {}

  public static String int_vars(PptTopLevel ppt, ValueTuple vt) {}

  public static String related_vars(PptTopLevel ppt, ValueTuple vt) {}

  public static String toString(/*@nullable@*/ Object val) {}

  public static String toString(VarInfo[] vis, ValueTuple vt) {}

  public static /*@nullable@*/ String add_track(String def) {}
}
