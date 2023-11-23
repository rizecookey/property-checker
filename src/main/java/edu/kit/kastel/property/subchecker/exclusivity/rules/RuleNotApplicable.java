package edu.kit.kastel.property.subchecker.exclusivity.rules;

import org.checkerframework.dataflow.cfg.node.Node;

import javax.lang.model.element.AnnotationMirror;

@SuppressWarnings("serial")
public class RuleNotApplicable extends Exception {
    public RuleNotApplicable(String name, Node node, String reason) {
        super(String.format(
                "Rule %s not applicable to %s (%s)",
                name, node, reason
        ));
    }

    public RuleNotApplicable(String name, AnnotationMirror offendingType, String reason) {
        super(String.format(
                "Rule %s not applicable, value is not %s (%s)",
                name, offendingType, reason
        ));

    }
}
