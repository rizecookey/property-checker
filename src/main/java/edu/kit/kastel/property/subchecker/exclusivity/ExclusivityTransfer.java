package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.MethodTree;

import edu.kit.kastel.property.subchecker.exclusivity.rules.*;

import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import javax.lang.model.element.AnnotationMirror;
import java.util.List;

public class ExclusivityTransfer extends CFTransfer {
    private final ExclusivityAnnotatedTypeFactory factory;

    public ExclusivityTransfer(CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis,
                               ExclusivityAnnotatedTypeFactory factory) {
        super(analysis);
        assert factory == analysis.getTypeFactory();
        this.factory = factory;
    }

    @Override
    public CFStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        CFStore store = super.initialStore(underlyingAST, parameters);
        /*for (CFAbstractAnalysis.FieldInitialValue val : store.get) {
            // Viewpoint-adapt field values? Should be done in atc#performanalysis where initial field values are set instead?
        }*/
        return store;
    }

    @Override
    public TransferResult<CFValue, CFStore> visitAssignment(
            AssignmentNode node, TransferInput<CFValue, CFStore> in) {
        CFStore store = in.getRegularStore();

        if (node.getExpression() instanceof MethodInvocationNode) {
            new TMethodInvocationHelper(store, factory, analysis)
                    .applyOrInvalidate(node.getTarget(), node.getExpression());
        } else {
            new TAssign(store, factory, analysis).applyOrInvalidate(node.getTarget(), node.getExpression());
        }

        return new RegularTransferResult<>(null, in.getRegularStore());
    }
    
    @Override
    public TransferResult<CFValue, CFStore> visitMethodAccess(MethodAccessNode n, TransferInput<CFValue, CFStore> p) {
        // TODO Auto-generated method stub
        return super.visitMethodAccess(n, p);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<CFValue, CFStore> in
    ) {
        CFStore store = in.getRegularStore();

        try {
            new TMethodInvocation(store, factory, analysis).apply(n);
        } catch (RuleNotApplicable e) {
            new TInvalidate(store, factory, analysis).apply(n);
        }

        return new RegularTransferResult<>(null, store);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitReturn(
            ReturnNode node, TransferInput<CFValue, CFStore> in) {
        CFStore store = in.getRegularStore();

        MethodTree methodTree = (MethodTree) factory.getEnclosingClassOrMethod(node.getTree());
        assert methodTree != null;
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(
                factory.getAnnotatedType(methodTree).getReturnType());

        new TAssign(store, factory, analysis).applyOrInvalidate(returnTypeAnno, node.getResult());

        return new RegularTransferResult<>(null, store);
    }
}
