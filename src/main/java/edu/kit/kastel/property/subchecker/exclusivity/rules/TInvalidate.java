package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ValueLiteralNode;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.javacutil.AnnotationMirrorSet;

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
        if (node instanceof ValueLiteralNode) {
            return;
        }

        ExclusivityValue abstractValue = analysis.createAbstractValue(
                AnnotationMirrorSet.singleton(factory.EXCL_BOTTOM), node.getType());
        store.replaceValue(JavaExpression.fromNode(node), abstractValue);
        System.err.printf("[~> ExclBottom] %s ...;\n", node);
        //System.out.println("Applied " + getName());
    }

    @Override
    public String getName() {
        return "U-Invalidate";
    }
}
