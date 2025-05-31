package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class MemMonitor {

  public MemMonitor(String filename) {}

  public void run() {}

  public void end_of_iteration(
      String pptName,
      int num_samples,
      int num_static_vars,
      int num_orig_vars,
      int num_scalar_vars,
      int num_array_vars,
      int num_derived_scalar_vars,
      int num_derived_array_vars) {}

  public void stop() {}
}
