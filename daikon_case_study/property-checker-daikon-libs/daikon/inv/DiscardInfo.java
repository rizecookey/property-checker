package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public final class DiscardInfo {

  public Invariant inv;

  public DiscardInfo(Invariant inv, DiscardCode discardCode, String discardString) {}

  public String discardFormat() {}

  public DiscardCode discardCode() {}

  public String discardString() {}

  public String className() {}

  public String format() {}

  public void add_implied(String reason) {}

  public void add_implied_vis(VarInfo[] vis) {}
}
