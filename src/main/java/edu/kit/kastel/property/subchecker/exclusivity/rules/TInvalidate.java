package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import java.util.Collections;

public class TInvalidate implements TypeRule {
    protected final CFStore store;
    protected final ExclusivityAnnotatedTypeFactory factory;
    protected CFAbstractAnalysis<CFValue, CFStore, CFTransfer>  analysis;

    public TInvalidate(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        this.store = store;
        this.analysis = analysis;
        this.factory = factory;
    }

    @Override
    public void apply(Node node) {
        CFValue abstractValue = analysis.createAbstractValue(
                AnnotationMirrorSet.singleton(factory.EXCL_BOTTOM), node.getType());
        store.replaceValue(JavaExpression.fromNode(node), abstractValue);
        System.out.printf("[~> ExclusivityBottom] %s ...;\n", node);
        System.out.println("Applied " + getName());
    }

    @Override
    public String getName() {
        return "U-Invalidate";
    }
}
