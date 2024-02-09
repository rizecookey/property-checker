package edu.kit.kastel.property.subchecker.exclusivity;

import java.util.Set;

import com.sun.source.tree.*;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;

public class ExclusivityPropagationTreeAnnotator extends PropagationTreeAnnotator {

    public ExclusivityPropagationTreeAnnotator(ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(atypeFactory);
    }

    // Primitives and strings are always @MaybeAliased

    @Override
    public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
        // The result of a binary operation is either primitive or a String,
        // thus MaybeAliased.
        type.addMissingAnnotations(Set.of(((ExclusivityAnnotatedTypeFactory) atypeFactory).MAYBE_ALIASED));
        return null;
    }

    @Override
    public Void visitUnary(UnaryTree node, AnnotatedTypeMirror type) {
        // The result of a unary operation is either primitive or a String,
        // thus MaybeAliased.
        type.addMissingAnnotations(Set.of(((ExclusivityAnnotatedTypeFactory) atypeFactory).MAYBE_ALIASED));
        return null;
    }
}
