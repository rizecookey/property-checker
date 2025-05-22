package daikon.diff;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** All visitors must implement this interface. */
public interface Visitor {

  public void visit(@NonNullNode RootNode node);

  public void visit(@NonNullNode PptNode node);

  public void visit(@NonNullNode InvNode node);
}
