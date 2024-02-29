package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import org.checkerframework.dataflow.cfg.node.Node;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.type.TypeKind;

public class TRefCopyPrimitive extends AssignmentRule {

    public TRefCopyPrimitive(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    public final void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        if (!rhsNode.getType().getKind().isPrimitive() && !rhsNode.getType().getKind().equals(TypeKind.NULL)) {
            throw new RuleNotApplicable(getName(), rhsNode, "not primitive");
        }

        updateType(lhsNode, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        if (!rhsNode.getType().getKind().isPrimitive() && !rhsNode.getType().getKind().equals(TypeKind.NULL)) {
            throw new RuleNotApplicable(getName(), rhsNode, "not primitive");
        }

        canUpdateType(lhsType, getNewLhsTypeAnnotation());
        updateType(rhsNode, getNewRhsTypeAnnotation());
    }

    protected AnnotationMirror getNewLhsTypeAnnotation() {
        return factory.UNIQUE;
    }

    protected AnnotationMirror getNewRhsTypeAnnotation() {
        return factory.UNIQUE;
    }

    @Override
    public String getName() {
        return "U-Ref-Copy-Primitive";
    }
}
