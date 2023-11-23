package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TRefNew extends AssignmentRule {

    public TRefNew(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        super(store, factory, analysis);
    }

    @Override
    public String getName() {
        return "T-Ref-New";
    }

    @Override
    public void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        checkRhsNode(rhsNode);
        try {
            updateType(lhsNode, factory.EXCL_MUT);
        } catch (RuleNotApplicable e) {
            // While a constructor result can be refined to ExclMut,
            // a constructor can also be made to return any other type.
            // So if the lhs is incompatible with ExclMut, we leave it as is.
        }
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        checkRhsNode(rhsNode);
        try {
            canUpdateType(lhsType, factory.EXCL_MUT);
        } catch (RuleNotApplicable e) {
            // While a constructor result can be refined to ExclMut,
            // a constructor can also be made to return any other type.
            // So if the lhs is incompatible with ExclMut, we leave it as is.
        }
    }

    private void checkRhsNode(Node rhsNode) throws RuleNotApplicable {
        if (!(rhsNode instanceof ObjectCreationNode)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs node is no object creation");
        }
    }
}
