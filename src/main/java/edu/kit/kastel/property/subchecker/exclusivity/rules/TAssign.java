package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TAssign extends AssignmentRule {
    public TAssign(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
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
        return "T-Assign";
    }
}
