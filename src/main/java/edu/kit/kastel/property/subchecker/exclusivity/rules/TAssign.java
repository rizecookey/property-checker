package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.cfg.node.Node;

import javax.lang.model.element.AnnotationMirror;

public class TAssign extends AssignmentRule {
    public TAssign(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    protected void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        ChainRule<AssignmentRule> rules = getAssignmentRules();
        rules.apply(lhsNode, rhsNode);
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        ChainRule<AssignmentRule> rules = getAssignmentRules();
        rules.apply(lhsType, rhsNode);
    }

    public void applyWithoutInvalidation(Node lhsNode, Node rhsNode) {
        try {
            applyInternal(lhsNode, rhsNode);
        } catch (RuleNotApplicable ignored) {
            // ignore
        }
    }

    public void applyWithoutInvalidation(AnnotationMirror lhsType, Node rhsNode) {
        try {
            applyInternal(lhsType, rhsNode);
        } catch (RuleNotApplicable ignored) {
            // ignore
        }
    }

    public void applyOrInvalidate(Node lhsNode, Node rhsNode) {
        try {
            applyInternal(lhsNode, rhsNode);
        } catch (RuleNotApplicable ignored) {
            // No valid rule to refine assignment, so it must be invalid.
            // ExclusivityVisitor will report the error.
            new TInvalidate(store, factory, analysis).apply(lhsNode);
            new TInvalidate(store, factory, analysis).apply(rhsNode);
        }
    }

    public void applyOrInvalidate(AnnotationMirror lhsType, Node rhsNode) {
        try {
            applyInternal(lhsType, rhsNode);
        } catch (RuleNotApplicable ignored) {
            // No valid rule to refine assignment, so it must be invalid.
            // ExclusivityVisitor will report the error.
            new TInvalidate(store, factory, analysis).apply(rhsNode);
        }
    }

    @Override
    public String getName() {
        return "U-Assign";
    }
}
