package daikon.diff;

import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;

/** The root of the tree. All its children are PptNodes. */
public class RootNode extends Node<Void, @NonNullNode PptNode> {

  /** Creates a new RootNode object. */
  @SuppressWarnings({"rawtypes", "unchecked"})
  public RootNode() {
    super(new Object(), new Object());
  }

  @Override
  public IPair<Void, Void> getUserObject() {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Pure
  @Override
  public Void getUserLeft() {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Pure
  @Override
  public Void getUserRight() {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Override
  public void accept(Visitor v) {
    v.visit(this);
  }
}
