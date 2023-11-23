package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

abstract class ExclMutAssignmentRule extends AssignmentRule {
    public ExclMutAssignmentRule(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        super(store, factory, analysis);
    }

    @Override
    public final void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        checkRhsTypeAnno(rhsNode);

        updateType(lhsNode, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        checkRhsTypeAnno(rhsNode);

        canUpdateType(lhsType, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    private void checkRhsTypeAnno(Node rhsNode) throws RuleNotApplicable {
        if (!hierarchy.isSubtype(getRefinedTypeAnnotation(rhsNode), factory.EXCL_MUT)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs is not ExclMut");
        }
    }

    protected abstract AnnotationMirror getNewLhsTypeAnnotation();
    protected abstract AnnotationMirror getNewRhsTypeAnnotation();
}
