package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class VarParent {

  private static final long serialVersionUID = 20130425L;

  public String parent_ppt;

  public /*@nullable@*/ String parent_variable;

  public int parent_relation_id;

  public VarParent(String parent_ppt, int parent_relation_id, /*@nullable@*/ String parent_variable) {}
}
