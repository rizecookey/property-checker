package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.type.TypeMirror;

public class TMethodInvocationHelper extends AssignmentRule {
    public TMethodInvocationHelper(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        super(store, factory, analysis);
    }

    @Override
    protected void applyInternal(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        MethodInvocationNode methodInvocationNode;
        try {
            methodInvocationNode = (MethodInvocationNode) rhsNode;
        } catch (ClassCastException ignored) {
            throw new RuleNotApplicable(getName(), rhsNode, "rhs is no method invocation");
        }

        applyInternal(lhsNode, methodInvocationNode);
    }

    protected void applyInternal(Node lhsNode, MethodInvocationNode rhsNode) throws RuleNotApplicable {
        TypeMirror returnType = rhsNode.getTarget().getMethod().getReturnType();
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(returnType.getAnnotationMirrors());
        updateType(lhsNode, returnTypeAnno);
    }

    public void applyOrInvalidate(Node lhsNode, Node rhsNode) {
        try {
            applyInternal(lhsNode, rhsNode);
        } catch (RuleNotApplicable ignored) {
            new TInvalidate(store, factory, analysis).apply(lhsNode);
        }
    }

    @Override
    protected void applyInternal(AnnotationMirror lhsType, Node rhsNode) {
        assert false : "Cannot be called";
    }

    @Override
    public String getName() {
        return null;
    }
}