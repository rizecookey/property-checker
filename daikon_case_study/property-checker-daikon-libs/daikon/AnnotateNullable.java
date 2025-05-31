package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class AnnotateNullable {

  static PptMap ppts = new PptMap();
  static Map class_map = new LinkedHashMap();
  static String last_package = "";
  public static boolean stub_format = false;
  public static boolean nonnull_annotations = false;

  private static /*@nullable@*/ PptTopLevel class_for_object(PptTopLevel object_ppt) {}

  public static void process_class(PptTopLevel object_ppt) {}

  public static String get_annotation(PptTopLevel ppt, VarInfo vi) {}

  public static void process_method(PptTopLevel ppt) {}

  public static void process_obj_fields(PptTopLevel ppt) {}

  public static String jvm_signature(PptTopLevel ppt) {}

  public static String field_name(VarInfo vi) {}

  public static boolean is_static_method(PptTopLevel ppt) {}
}
