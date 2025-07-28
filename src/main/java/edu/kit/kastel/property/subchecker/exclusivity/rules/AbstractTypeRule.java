package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.AnnotationMirror;

abstract class AbstractTypeRule<N extends Node> implements TypeRule {

    /*
     * If store is null, type rule shall just check for applicability without actually refining types.
     */
    protected final @Nullable ExclusivityStore store;
    protected final QualifierHierarchy hierarchy;
    protected final ExclusivityAnnotatedTypeFactory factory;
    protected @Nullable ExclusivityAnalysis analysis;

    public AbstractTypeRule(@Nullable ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory,
                            ExclusivityAnalysis analysis) {
        this.store = store;
        this.analysis = analysis;
        this.hierarchy = factory.getQualifierHierarchy();
        this.factory = factory;
    }

    @Override
    public final void apply(Node abstractNode) throws RuleNotApplicable {
        N node;
        try {
            @SuppressWarnings("unchecked")
            N concreteNode = (N) abstractNode;
            node = concreteNode;
        } catch (ClassCastException e) {
            throw new RuleNotApplicable(getName(), abstractNode, "wrong node type");
        }
        applyInternal(node);
        /*if (getName() != null) {
            System.out.println("Applied " + getName());
        }*/
    }

    protected abstract void applyInternal(N node) throws RuleNotApplicable;

    /**
     * Update type of node in store to newRefinedType, ensuring that newRefinedType
     * is a subtype of node's declared type.
     *
     * @param node        The node whose type is to be updated
     * @param refinedType The new, refined type of node
     * @throws RuleNotApplicable if the refinement would violate the declaration
     */
    protected final void updateType(
            Node node, AnnotationMirror refinedType
    ) throws RuleNotApplicable {
        updateType(node, refinedType, true);
    }

    /**
     * Update type of node in store to newRefinedType.
     *
     * @param node        The node whose type is to be updated
     * @param refinedType The new, refined type of node
     * @param checkValidity Whether to check that newRefinedType is a subtype of node's declared type
     * @throws RuleNotApplicable if the refinement would violate the declaration
     */
    protected final void updateType(
            Node node, AnnotationMirror refinedType, boolean checkValidity
    ) throws RuleNotApplicable {
        // Cannot update the type of a non-lhs expression in the store,
        // so we just check if the old type fits.
        if (!isLhs(node)) {
            if (AnnotationUtils.areSame(getRefinedTypeAnnotation(node), refinedType)) {
                return;
            } else {
                throw new RuleNotApplicable(
                        getName(), getRefinedTypeAnnotation(node), "refinement violates non-lhs expression type");
            }
        }

        if (checkValidity) {
            canUpdateType(node, refinedType);
        }

        if (store != null && analysis != null) {
            ExclusivityValue abstractValue = analysis.createAbstractValue(
                AnnotationMirrorSet.singleton(refinedType), node.getType());
            store.replaceValue(JavaExpression.fromNode(node),
                    abstractValue);
        }
    }

    protected final boolean isLhs(Node node) {
        if (node instanceof ImplicitThisNode) {
            return true;
        }
        switch (node.getTree().getKind()) {
            case VARIABLE:
            case IDENTIFIER:
            case MEMBER_SELECT:
            case ARRAY_ACCESS:
            case PARENTHESIZED:
                return true;
            default:
                return TreeUtils.isTypeTree(node.getTree());
        }
    }

    protected final void canUpdateType(Node node, AnnotationMirror refinedType)
            throws RuleNotApplicable {
        // Does nothing.
        // Local variables have a declared type that's only used to determine what rule to use when assigning to them.
        // It can be violated.
        // Field type can be violated too if the receiver is sufficiently unpacked.
    }

    protected final void canUpdateType(AnnotationMirror declTypeAnno, AnnotationMirror refinedType)
            throws RuleNotApplicable {
        if (!isValidRefinement(declTypeAnno, refinedType)) {
            throw new RuleNotApplicable(getName(), declTypeAnno, "refinement violates declaration");
        }
    }

    protected final boolean isValidRefinement(AnnotationMirror declaredType, AnnotationMirror refinedType) {
        assert declaredType != null;
        return hierarchy.isSubtypeQualifiersOnly(refinedType, declaredType);
    }

    protected AnnotationMirror getUnadaptedTypeAnnotation(Node node) {
        if (node instanceof FieldAccessNode) {
            return factory.getExclusivityAnnotation(factory.getAnnotatedType(((FieldAccessNode) node).getElement()).getAnnotations());
        }

        return factory.getExclusivityAnnotation(
                // TODO Do we need to get declared types for nodes not supported by getAnnotatedTypeLhs?
                factory.getAnnotatedTypeLhs(node.getTree()).getAnnotations());
    }

    protected AnnotationMirror getAdaptedTypeAnnotation(Node node) {
        return factory.getExclusivityAnnotation(
                // TODO Do we need to get declared types for nodes not supported by getAnnotatedTypeLhs?
                factory.getAnnotatedTypeLhs(node.getTree()).getAnnotations());
    }

    protected final AnnotationMirror getRefinedTypeAnnotation(Node node) {
        AnnotationMirror oldAnno;
        ExclusivityValue value = null;
        if (node instanceof FieldAccessNode) {
            value = store.getValue((FieldAccessNode) node);
        } else if (node instanceof LocalVariableNode) {
            value = store.getValue((LocalVariableNode) node);
        } else if (node instanceof ThisNode) {
            value = store.getValue((ThisNode) node);
        }

        if (value != null && !value.getAnnotations().isEmpty()) {
            oldAnno = factory.getExclusivityAnnotation(value.getAnnotations());
        } else if (node.getTree() != null) {
            oldAnno = factory.getExclusivityAnnotation(factory.getAnnotatedType(node.getTree()).getEffectiveAnnotations());
        } else {
            oldAnno = factory.MAYBE_ALIASED;
        }
        assert oldAnno != null;
        return oldAnno;
    }

    protected final String prettyPrint(@Nullable AnnotationMirror anno) {
        // TODO: There has to be a better way to do this
        String pkgName = "edu.kit.kastel.property.subchecker.exclusivity.qual.";
        StringBuilder s = new StringBuilder(anno != null ? anno.toString() : "");
        if (s.length() > 0) {
            s.delete(s.indexOf(pkgName), s.indexOf(pkgName) + pkgName.length());
        }
        return s.toString();
    }
}
