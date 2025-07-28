package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public enum OutputFormat {

  DAIKON("Daikon"),
  DBCJAVA("DBC"),
  ESCJAVA("ESC/Java"),
  JAVA("Java"),
  JML("JML"),
  SIMPLIFY("Simplify"),
  CSHARPCONTRACT("CSharpContract");

  final String name;

  OutputFormat(String name) {}

  public boolean isJavaFamily() {}

  public static OutputFormat get(String name) {}

  public String ensures_tag() {}

  public String requires_tag() {}
}
