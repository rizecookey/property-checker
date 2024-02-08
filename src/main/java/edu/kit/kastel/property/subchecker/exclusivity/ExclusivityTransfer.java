package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.rules.*;

import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

public class ExclusivityTransfer extends PackingClientTransfer<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> {

    private final ExclusivityAnnotatedTypeFactory factory;

    public ExclusivityTransfer(ExclusivityAnalysis analysis,
                               ExclusivityAnnotatedTypeFactory factory) {
        super(analysis);
        assert factory == analysis.getTypeFactory();
        this.factory = factory;
    }

    public ExclusivityAnalysis getAnalysis() {
        return (ExclusivityAnalysis) analysis;
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitAssignment(
            AssignmentNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        if (node.getExpression() instanceof MethodInvocationNode) {
            new TMethodInvocationHelper(store, factory, getAnalysis())
                    .applyOrInvalidate(node.getTarget(), node.getExpression());
        } else {
            new TAssign(store, factory, getAnalysis()).applyOrInvalidate(node.getTarget(), node.getExpression());
        }

        return new RegularTransferResult<>(null, in.getRegularStore());
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<ExclusivityValue, ExclusivityStore> in
    ) {
        ExclusivityStore store = in.getRegularStore();
        ExpressionTree invocationTree = n.getTree();
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();

        if (receiver instanceof ClassNameNode && ((ClassNameNode) receiver).getElement().toString().equals(Packing.class.getName())) {
            // Packing statements don't change the store
            return new RegularTransferResult<>(null, store, false);
        }

        try {
            new TMethodInvocation(store, factory, getAnalysis()).apply(n);
        } catch (RuleNotApplicable e) {
            new TInvalidate(store, factory, getAnalysis()).apply(n);
        }

        processPostconditions(n, store, method, invocationTree);

        return new RegularTransferResult<>(null, store, true);
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitReturn(
            ReturnNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        MethodTree methodTree = (MethodTree) factory.getEnclosingClassOrMethod(node.getTree());
        assert methodTree != null;
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(
                factory.getAnnotatedType(methodTree).getReturnType());

        new TAssign(store, factory, getAnalysis()).applyOrInvalidate(returnTypeAnno, node.getResult());

        return new RegularTransferResult<>(null, store);
    }

    //TODO handle constructors
}
