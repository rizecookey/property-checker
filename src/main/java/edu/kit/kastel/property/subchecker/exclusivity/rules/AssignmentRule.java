package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.dataflow.cfg.node.AssignmentNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ValueLiteralNode;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.Unknown;
import org.checkerframework.javacutil.BugInCF;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;

public abstract class AssignmentRule extends AbstractTypeRule<AssignmentNode> {

    public AssignmentRule(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        super(store, factory, analysis);
    }

    @Override
    protected final void applyInternal(AssignmentNode node) throws RuleNotApplicable {
        apply(node.getTarget(), node.getExpression());
    }

    public final void apply(Node lhs, Node rhs) throws RuleNotApplicable {
        AnnotationMirror oldLhs = getRefinedTypeAnnotation(lhs);
        AnnotationMirror oldRhs = getRefinedTypeAnnotation(rhs);
        applyInternal(lhs, rhs);
        //printAssignment(lhs, oldLhs, rhs, oldRhs);
    }

    public final void apply(AnnotationMirror lhsType, Node rhs) throws RuleNotApplicable {
        AnnotationMirror oldRhs = getRefinedTypeAnnotation(rhs);
        applyInternal(lhsType, rhs);
        //printTypeChange(rhs, oldRhs);
        //System.out.print(",");
    }

    protected abstract void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable;
    protected abstract void applyInternal(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable;

    private void printAssignment(Node lhsNode, AnnotationMirror oldLhsTypeAnno,
                                 Node rhsNode, AnnotationMirror oldRhsTypeAnno) {
        printTypeChange(lhsNode, oldLhsTypeAnno);
        //System.out.print(" = ");
        printTypeChange(rhsNode, oldRhsTypeAnno);
        //System.out.println(";");
    }

    private void printTypeChange(Node node, AnnotationMirror oldTypeAnno) {
        if (store != null && !(JavaExpression.fromNode(node) instanceof Unknown)) {
            AnnotationMirror newTypeAnno = oldTypeAnno;
            ExclusivityValue value;
            if (node instanceof ValueLiteralNode) {
                /*System.out.printf("[%s ~> %s] ",
                        prettyPrint(oldTypeAnno),
                        prettyPrint(factory.MAYBE_ALIASED));*/
            } else {
                try {
                    value = store.getValue(JavaExpression.fromNode(node));
                } catch (BugInCF b) { // Expression type not supported by store
                    value = null;
                }
                if (value != null) {
                    newTypeAnno = factory.getExclusivityAnnotation(value.getAnnotations());
                }
                /*System.out.printf("[%s ~> %s] ",
                        prettyPrint(oldTypeAnno),
                        prettyPrint(newTypeAnno));*/
            }
        }
        //System.out.print(node);
    }

    protected final ChainRule<AssignmentRule> getAssignmentRules() {
        return new ChainRule<>(
                new TRefNew(store, factory, analysis),
                new TRefCopyPrimitive(store, factory, analysis),
                new TRefSplit(store, factory, analysis),
                new TRefTransfer(store, factory, analysis),
                new TRefCopyRo(store, factory, analysis)
        );
    }
}
