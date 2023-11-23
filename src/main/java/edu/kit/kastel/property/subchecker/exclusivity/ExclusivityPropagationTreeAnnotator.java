package edu.kit.kastel.property.subchecker.exclusivity;

import java.util.Set;

import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;

import com.sun.source.tree.BinaryTree;

public class ExclusivityPropagationTreeAnnotator extends PropagationTreeAnnotator {

    public ExclusivityPropagationTreeAnnotator(ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(atypeFactory);
    }

    @Override
    public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
        // The result of a binary operation is either primitive or a String,
        // thus immutable.
        type.addMissingAnnotations(Set.of(((ExclusivityAnnotatedTypeFactory) atypeFactory).IMMUTABLE));
        return null;
    }
}
