package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class DynamicConstants {

  static final long serialVersionUID = 20040401L;
  static final boolean no_post_process = false;
  public static boolean dkconfig_use_dynamic_constant_optimization = true;
  public static boolean dkconfig_OneOf_only = false;
  //public static final Logger debug = Logger.getLogger("daikon.DynamicConstants");
  List con_list = new ArrayList();
  List missing_list = new ArrayList();
  Constant[] all_vars;
  List all_list = new ArrayList();
  PptTopLevel ppt;
  int sample_cnt = 0;

  public static class Constant implements Serializable {

    static final long serialVersionUID = 20030913L;

    public /*@nullable@*/ Object val = null;
    public int count = 0;
    public VarInfo vi;
    boolean always_missing = true;
    boolean constant = false;
    boolean previously_constant = false;
    boolean previous_missing = false;

    public void checkRep() {}

    public Constant(VarInfo vi) {}

    public /*@pure@*/ boolean is_prev_constant() {}
  }

  public static final class ConIndexComparator {
    static final long serialVersionUID = 20050923L;

    private ConIndexComparator() {}


    public static ConIndexComparator getInstance() {}

    static final ConIndexComparator theInstance = new ConIndexComparator();
  }

  public DynamicConstants(PptTopLevel ppt) {}

  public void add(ValueTuple vt, int count) {}

  /*@pure@*/ public Constant getConstant(VarInfo vi) {}

  /*@pure@*/public boolean is_constant(VarInfo vi) {}

  /*@pure@*/ public boolean is_prev_constant(VarInfo vi) {}

  public Object constant_value(VarInfo vi) {}

  /*@pure@*/ public boolean is_missing(VarInfo vi) {}

  /*@pure@*/ public boolean is_prev_missing(VarInfo vi) {}

  public int constant_leader_cnt() {}

  public void instantiate_new_views(List noncons, List non_missing) {}

  public void instantiate_constant_suppressions(List new_noncons, List all) {}

  public void post_process() {}

  public List create_constant_invs() {}

  //public void print_missing(PrintWriter out) {}

  public void merge() {}

  public void instantiate_oneof(Constant con) {}
}
