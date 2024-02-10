package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.expression.JavaExpression;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import java.util.Collections;

public class TInvalidate implements TypeRule {
    protected final ExclusivityStore store;
    protected final ExclusivityAnnotatedTypeFactory factory;
    protected ExclusivityAnalysis analysis;

    public TInvalidate(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
        this.store = store;
        this.analysis = analysis;
        this.factory = factory;
    }

    @Override
    public void apply(Node node) {
        ExclusivityValue abstractValue = analysis.createAbstractValue(
                AnnotationMirrorSet.singleton(factory.EXCL_BOTTOM), node.getType());
        store.replaceValue(JavaExpression.fromNode(node), abstractValue);
        //System.out.printf("[~> ExclusivityBottom] %s ...;\n", node);
        //System.out.println("Applied " + getName());
    }

    @Override
    public String getName() {
        return "U-Invalidate";
    }
}
