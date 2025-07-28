package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;

public interface TypeRule {
    void apply(Node node) throws RuleNotApplicable;
    String getName();
}
