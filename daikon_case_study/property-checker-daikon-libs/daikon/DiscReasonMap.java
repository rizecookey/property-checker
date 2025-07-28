package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public final class DiscReasonMap {


  private DiscReasonMap() {}

  public static void initialize() {}

  public static void put(Invariant inv, DiscardInfo disc_info) {}

  public static void put(Invariant inv, DiscardCode discardCode, String discardString) {}

  public static void put(String vars, String ppt, DiscardInfo disc_info) {}

  public static List returnMatches_from_ppt(InvariantInfo invInfo) {}

  private static List all_vars_tied_from_ppt(String ppt) {}

  public static void debugVarMap(String ppt) {}
}
