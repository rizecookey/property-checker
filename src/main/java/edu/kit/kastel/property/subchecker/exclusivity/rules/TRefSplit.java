package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TRefSplit extends AssignmentRule {
    public TRefSplit(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    public final void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        checkRhsTypeAnno(rhsNode);

        if (hierarchy.isSubtypeQualifiersOnly(getRefinedTypeAnnotation(rhsNode), factory.UNIQUE)
                && !hierarchy.isSubtypeQualifiersOnly(getDeclaredTypeAnnotation(lhsNode), factory.MAYBE_ALIASED)) {
            // Apply TRefCopyRo instead
            throw new RuleNotApplicable(getName(), rhsNode, "copy as ReadOnly instead of splitting");
        }

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
        if (!hierarchy.isSubtypeQualifiersOnly(getRefinedTypeAnnotation(rhsNode), factory.MAYBE_ALIASED)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs is ReadOnly");
        }
    }

    protected AnnotationMirror getNewLhsTypeAnnotation() {
        return factory.MAYBE_ALIASED;
    }

    protected AnnotationMirror getNewRhsTypeAnnotation() {
        return factory.MAYBE_ALIASED;
    }

    @Override
    public String getName() {
        return "U-Ref-Split";
    }
}
