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
    for (Iterator<@NonNullNode PptNode> i = node.children(); i.hasNext(); ) {
      // The cast is necessary because KeY does not support generics
      ((@NonNullNode PptNode)i.next()).accept(this);
    }
  }

  @Override
  public void visit(@NonNullNode PptNode node) {
    for (Iterator<@NonNullNode InvNode> i = node.children(); i.hasNext(); ) {
      // The cast is necessary because KeY does not support generics
      ((@NonNullNode InvNode)i.next()).accept(this);
    }
  }

  @Override
  public void visit(@NonNullNode InvNode node) {}
}
