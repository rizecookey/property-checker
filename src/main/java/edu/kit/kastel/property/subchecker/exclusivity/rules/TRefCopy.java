package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TRefCopy extends AssignmentRule {
    public TRefCopy(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        super(store, factory, analysis);
    }

    @Override
    public void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        updateType(lhsNode, getAndCheckRhsTypeAnno(rhsNode));
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsTypeAnno, Node rhsNode) throws RuleNotApplicable {
        canUpdateType(lhsTypeAnno, getAndCheckRhsTypeAnno(rhsNode));
    }

    private AnnotationMirror getAndCheckRhsTypeAnno(Node rhsNode) throws RuleNotApplicable {
        AnnotationMirror oldRhsTypeAnno = getRefinedTypeAnnotation(rhsNode);
        if (!factory.isCopyable(oldRhsTypeAnno)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs node is not copyable");
        }

        return oldRhsTypeAnno;
    }

    @Override
    public String getName() {
        return "T-Ref-Copy";
    }
}
