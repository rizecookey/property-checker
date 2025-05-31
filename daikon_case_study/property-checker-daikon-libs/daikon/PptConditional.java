package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class PptConditional extends PptTopLevel {

  static final long serialVersionUID = 20041216L;
  public PptTopLevel parent;
  //public transient Splitter splitter;
  public boolean splitter_inverse;

  //public PptConditional(PptTopLevel parent, Splitter splitter, boolean splitter_inverse) {}

  public boolean splitter_valid() {}

  public /*@nullable@*/ DummyInvariant dummyInvariant() {}
}
