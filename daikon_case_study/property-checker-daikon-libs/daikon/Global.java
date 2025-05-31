package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class Global {

  private Global() {}

  public static final String lineSep;
  //public static final java.util.regex.Pattern ws_regexp;
  //public static final Random random = new Random();

  public static final boolean output_statistics = true;
  public static int non_canonical_variables = 0;
  public static int can_be_missing_variables = 0;
  public static int canonical_variables = 0;
  public static int nonsensical_suppressed_derived_variables = 0;
  public static int tautological_suppressed_derived_variables = 0;
  public static int derived_variables = 0;
  public static int implied_noninstantiated_invariants = 0;
  public static int implied_false_noninstantiated_invariants = 0;
  public static int subexact_noninstantiated_invariants = 0;
  public static int partially_implied_invariants = 0;
  public static int instantiated_invariants = 0;
  public static int falsified_invariants = 0;
  public static int non_falsified_invariants = 0;
  public static int too_few_samples_invariants = 0;
  public static int non_canonical_invariants = 0;
  public static int obvious_invariants = 0;
  public static int unjustified_invariants = 0;
  public static int reported_invariants = 0;

  public static void output_statistics() {}

  //public static boolean debugAll = false;
  //public static final Logger debugStatistics = Logger.getLogger("daikon.statistics");
  //public static final Logger debugSimplify = Logger.getLogger("daikon.simplify");
  //public static Logger debugDerive = Logger.getLogger("daikon.derive");
  //public static Logger debugSplit = Logger.getLogger("daikon.split");
  //public static Logger debugInfer = Logger.getLogger("daikon.infer");
  //public static Logger debugSuppress = Logger.getLogger("daikon.suppress");
  //public static Logger debugSuppressParam = Logger.getLogger("daikon.suppress.param");
  //public static final boolean debugPrintDtrace = false;
  //public static @Owning @MonotonicNonNull PrintWriter dtraceWriter = null;
  //public static FuzzyFloat fuzzy = new FuzzyFloat();
  //public static Map<PptTopLevel, List<PptTopLevel.Stats>> stats_map = new LinkedHashMap<>();
}
