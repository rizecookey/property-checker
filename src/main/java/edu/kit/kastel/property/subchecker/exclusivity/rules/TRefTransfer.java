package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.cfg.node.Node;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public class TRefTransfer extends AssignmentRule {

    public TRefTransfer(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    public final void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        checkRhsTypeAnno(rhsNode);

        if (hierarchy.isSubtypeQualifiersOnly(getRefinedTypeAnnotation(rhsNode), factory.UNIQUE)
                && !hierarchy.isSubtypeQualifiersOnly(getUnadaptedTypeAnnotation(lhsNode), factory.MAYBE_ALIASED)) {
            // Apply TRefCopyRo instead
            throw new RuleNotApplicable(getName(), rhsNode, "copy as ReadOnly instead of transferring");
        }

        updateType(lhsNode, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        checkRhsTypeAnno(rhsNode);

        if (hierarchy.isSubtypeQualifiersOnly(getRefinedTypeAnnotation(rhsNode), factory.UNIQUE)
                && !hierarchy.isSubtypeQualifiersOnly(lhsType, factory.MAYBE_ALIASED)) {
            // Apply TRefCopyRo instead
            throw new RuleNotApplicable(getName(), rhsNode, "copy as ReadOnly instead of transferring");
        }

        canUpdateType(lhsType, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    private void checkRhsTypeAnno(Node rhsNode) throws RuleNotApplicable {
        if (!hierarchy.isSubtypeQualifiersOnly(getRefinedTypeAnnotation(rhsNode), factory.UNIQUE)) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs is not Unique");
        }
    }

    protected AnnotationMirror getNewLhsTypeAnnotation() {
        return factory.UNIQUE;
    }

    protected AnnotationMirror getNewRhsTypeAnnotation() {
        return factory.READ_ONLY;
    }

    @Override
    public String getName() {
        return "U-Ref-Transfer";
    }
}
