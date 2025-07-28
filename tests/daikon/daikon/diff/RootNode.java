package daikon.diff;

import org.checkerframework.checker.nullness.qual.*;
import org.checkerframework.dataflow.qual.Pure;

import edu.kit.kastel.property.subchecker.lattice.daikon_qual.*;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

/** The root of the tree. All its children are PptNodes. */
public class RootNode extends Node<@Nullable @MaybeAliased Void, @NonNullNode @MaybeAliased PptNode> {

  /** Creates a new RootNode object. */
  @SuppressWarnings({"rawtypes", "unchecked"})
  @Pure
  public RootNode() {
    // :: error: nullnessnode.argument.type.incompatible
    super(null, null);
  }

  @Pure
  @Override
  public IPair<Void, Void> getUserObject(@NonNullNode RootNode this) {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Pure
  @Override
  // not provable in KeY
  // :: error: nullnessnode.override.return.invalid
  public @NonNullIfNull("userObject.second") Void getUserLeft(@NonNullNode RootNode this) {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Pure
  @Override
  // not provable in KeY
  // :: error: nullnessnode.override.return.invalid
  public @NonNullIfNull("userObject.first") Void getUserRight(@NonNullNode RootNode this) {
    throw new Error("Shouldn't ask for userObject for RootNode");
  }

  @Override
  public void add(@NullableNode RootNode this, @NonNullNode PptNode newChild) {
    // Ill-typed, but prettier than making the children field non-private
    // :: error: nullnessnode.method.invocation.invalid
    super.add(newChild);
  }

  @Override
  public void accept(@NonNullNode RootNode this, Visitor v) {
    v.visit(this);
  }
}
