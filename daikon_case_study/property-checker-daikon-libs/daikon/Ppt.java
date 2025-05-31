package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public abstract class Ppt {

  protected Ppt(VarInfo[] var_infos) {}

  public static String varNames(VarInfo[] infos) {}

  public /*@helper@*/ String varNames() {}

  public /*@helper@*/ int indexOf(String varname) {}

  public /*@helper@*/ /*@nullable@*/ VarInfo find_var_by_name(String varname) {}

  public boolean containsVar(VarInfo vi) {}

  public abstract /*@helper@*/ String name();

  public static final class NameComparator {

    public int compare(PptTopLevel p1, PptTopLevel p2) {}

    static String swap(String s, char a, char b) {}
  }
}
