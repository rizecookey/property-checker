package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class PptMap {

  static final long serialVersionUID = 20040921L;

  public void add(PptTopLevel ppt) {}

  public void addAll(List ppts) {}

  /*@pure@*/ public /*@nullable@*/ PptTopLevel get(String name) {}

  /*@pure@*/ public /*@nullable@*/ PptTopLevel get(PptName name) {}

  // @EnsuresNonNullIf(result = true, expression = "get(#1)")
  /*@pure@*/ public boolean containsName(String name) {}

  public Collection all_ppts() {}

  public Collection asCollection() {}

  public Collection nameStringSet() {}

  public Iterator pptIterator() {}

  public Iterable pptIterable() {}

  public Iterator ppt_all_iterator() {}

  public Iterable ppt_all_iterable() {}

  public void trimToSize() {}

  public void repCheck() {}

  /*@pure@*/ public int countSlices() {}

  /*@pure@*/ public int size() {}

  public void removeUnsampled() {}
}
