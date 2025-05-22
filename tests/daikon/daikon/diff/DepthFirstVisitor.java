package daikon.diff;

import java.util.Iterator;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/**
 * Provides default methods which visit each node in the tree in depth-first order. Other visitors
 * may extend this class.
 */
public class DepthFirstVisitor implements Visitor {

  @Override
  public void visit(@NonNullNode RootNode node) {
    for (Iterator<PptNode> i = node.children(); i.hasNext(); ) {
      i.next().accept(this);
    }
  }

  @Override
  public void visit(@NonNullNode PptNode node) {
    for (Iterator<InvNode> i = node.children(); i.hasNext(); ) {
      i.next().accept(this);
    }
  }

  @Override
  public void visit(@NonNullNode InvNode node) {}
}
