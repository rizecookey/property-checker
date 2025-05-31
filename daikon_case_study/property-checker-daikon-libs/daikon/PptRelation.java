package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class PptRelation {

  static final long serialVersionUID = 20030819L;

  public enum PptRelationType {
    PARENT,
    USER,
    ENTER_EXIT,
    EXIT_EXITNN,
    MERGE_CHILD,
    PPT_PPTCOND
  };

  PptRelationType relationship;
  public PptTopLevel parent;
  public PptTopLevel child;
  public Map parent_to_child_map;
  public Map child_to_parent_map;
  public static boolean dkconfig_enable_object_user = false;

  /*@pure@*/ public int size() {}

  public String parent_to_child_var_string() {}

  public boolean relate_same_name() {}

  //public void debug_print_tree(Logger l, int indent) {}

  /*@pure@*/ public boolean is_primary() {}

  public PptRelationType getRelationType() {}

  public /*@nullable@*/ VarInfo parentVar(VarInfo childVar) {}

  public /*@nullable@*/ VarInfo parentVarAnyInEquality(VarInfo childVar) {}

  public /*@nullable@*/ VarInfo childVar(VarInfo parentVar) {}

  public boolean hasChildren() {}

  public Map get_child_equalities_as_parent() {}

  public static PptRelation newObjectMethodRel(PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newClassObjectRel(PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newParentRelation(FileIO.ParentRelation pr, PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newObjectUserRel(PptTopLevel parent, PptTopLevel child, VarInfo arg) {}

  public static PptRelation newEnterExitRel(PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newCombinedExitExitNNRel(PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newPptPptConditional(PptTopLevel parent, PptTopLevel child) {}

  public static PptRelation newMergeChildRel(PptTopLevel parent, PptTopLevel child) {}

  public PptRelation copy(PptTopLevel new_parent, PptTopLevel new_child) {}

  public static void init_hierarchy(PptMap all_ppts) {}

  public static void init_hierarchy_new(PptMap all_ppts) {}
}
