package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;

import javax.lang.model.element.AnnotationMirror;
import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class ChainRule<R extends AssignmentRule> implements TypeRule {
    List<R> typeRules;

    @SafeVarargs
    public ChainRule(R... typeRules) {
        this.typeRules = new ArrayList<R>(typeRules.length);
        for (R rule : typeRules) {
            this.typeRules.add(rule);
        }
    }

    @Override
    public void apply(Node node) throws RuleNotApplicable {
       apply(rule -> rule.apply(node), node);
    }

    public void apply(AnnotationMirror lhsType, Node rhsNode) throws RuleNotApplicable {
        apply(rule -> rule.apply(lhsType, rhsNode), rhsNode);
    }

    public void apply(Node lhsNode, Node rhsNode) throws RuleNotApplicable {
        apply(rule -> rule.apply(lhsNode, rhsNode), rhsNode);
    }

    private void apply(ThrowingConsumer<R, RuleNotApplicable> applicator, Node node) throws RuleNotApplicable {
        for (int i = 0; i < typeRules.size(); ++i) {
            R rule = typeRules.get(i);
            try {
                applicator.call(rule);
                break;
            } catch (RuleNotApplicable ignored) {
                if (i == typeRules.size() - 1) {
                    throw new RuleNotApplicable(getName(), node, "no rule was applicable");
                }
            }
        }
    }

    @FunctionalInterface
    private interface ThrowingConsumer<T, E extends Throwable> {
       void call(T param) throws E;
    }

    @Override
    public String getName() {
        return typeRules.stream().map(TypeRule::getName).collect(Collectors.joining(","));
    }
}
