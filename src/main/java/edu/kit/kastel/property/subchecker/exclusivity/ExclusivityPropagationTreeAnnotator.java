package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.BinaryTree;
import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.UnaryTree;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;

import javax.lang.model.type.TypeKind;

public class ExclusivityPropagationTreeAnnotator extends PropagationTreeAnnotator {

    public ExclusivityPropagationTreeAnnotator(ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(atypeFactory);
    }

    // Primitives are always @Unique
    // Using @Unique instead of @MaybeAliased is sound for immutable types,
    // but we use @MaybeAliased for Strings to mark them as immutable.

    @Override
    public Void visitBinary(BinaryTree node, AnnotatedTypeMirror type) {
        if (type.getPrimitiveKind() != null) {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).UNIQUE);
        } else {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).MAYBE_ALIASED);
        }
        return null;
    }

    @Override
    public Void visitUnary(UnaryTree node, AnnotatedTypeMirror type) {
        if (type.getPrimitiveKind() != null) {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).UNIQUE);
        } else {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).MAYBE_ALIASED);
        }
        return null;
    }

    @Override
    public Void visitLiteral(LiteralTree node, AnnotatedTypeMirror type) {
        if (type.getPrimitiveKind() != null || type.getKind() == TypeKind.NULL) {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).UNIQUE);
        } else {
            type.replaceAnnotation(((ExclusivityAnnotatedTypeFactory) atypeFactory).MAYBE_ALIASED);
        }
        return null;
    }
}
