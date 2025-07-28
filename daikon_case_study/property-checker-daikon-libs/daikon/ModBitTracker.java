package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class ModBitTracker implements Cloneable {

  static final long serialVersionUID = 20031014L;

  public ModBitTracker(int num_vars) {}

  public int num_vars() {}

  public int num_samples() {}

  public int num_sets() {}

  public /*@pure@*/ /*@helper@*/ void checkRep() {}

  //public BitSet get(int varindex) {}

  public boolean get(int varindex, int sampleno) {}

  public void add(ValueTuple vt, int count) {}
}
