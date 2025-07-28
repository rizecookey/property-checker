package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public class DiscardCode {

  static final long serialVersionUID = 20031016L;
  public static final DiscardCode obvious = new DiscardCode(0);
  public static final DiscardCode bad_sample = new DiscardCode(1);
  public static final DiscardCode bad_confidence = new DiscardCode(2);
  public static final DiscardCode not_enough_samples = new DiscardCode(4);
  public static final DiscardCode non_canonical_var = new DiscardCode(5);
  public static final DiscardCode implied_post_condition = new DiscardCode(6);
  public static final DiscardCode only_constant_vars = new DiscardCode(7);
  public static final DiscardCode derived_param = new DiscardCode(8);
  public static final DiscardCode unmodified_var = new DiscardCode(9);
  public static final DiscardCode control_check = new DiscardCode(10);
  public static final DiscardCode exact = new DiscardCode(11);
  public static final DiscardCode var_filtered = new DiscardCode(12);
  public static final DiscardCode filtered = new DiscardCode(13);
  public final int enumValue;

  private DiscardCode() {}

  private DiscardCode(int enumValue) {}

  /*@pure@*/ public int compareTo(DiscardCode o) {}

  //public static DiscardCode findCode(InvariantFilter filter) {}

  //public Object readResolve() throws ObjectStreamException {}
}
