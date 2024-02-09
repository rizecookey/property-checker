package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import edu.kit.kastel.property.packing.PackingClientAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessTreeAnnotator;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.Unknown;
import org.checkerframework.framework.flow.*;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;

import java.util.*;

public final class ExclusivityAnnotatedTypeFactory
        extends PackingClientAnnotatedTypeFactory<ExclusivityValue, ExclusivityStore, ExclusivityTransfer, ExclusivityAnalysis> {

    public final AnnotationMirror EXCL_BOTTOM =
            AnnotationBuilder.fromClass(elements, ExclBottom.class);
    public final AnnotationMirror UNIQUE =
            AnnotationBuilder.fromClass(elements, Unique.class);
    public final AnnotationMirror READ_ONLY =
            AnnotationBuilder.fromClass(elements, ReadOnly.class);
    public final AnnotationMirror MAYBE_ALIASED =
            AnnotationBuilder.fromClass(elements, MaybeAliased.class);

    private @Nullable Tree useIFlowAfter;

    public ExclusivityAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    public AnnotationMirror getDefaultPrimitiveQualifier() {
        return MAYBE_ALIASED;
    }

    @Override
    public ExclusivityTransfer createFlowTransferFunction(CFAbstractAnalysis<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> analysis) {
        return new ExclusivityTransfer((ExclusivityAnalysis) analysis, this);
    }

    public AnnotationMirror getExclusivityAnnotation(Collection<? extends AnnotationMirror> qualifiers) {
        for (AnnotationMirror qualifier : qualifiers) {
            try {
                if (qualHierarchy.isSubtypeQualifiersOnly(qualifier, READ_ONLY)) {
                    return qualifier;
                }
            } catch (BugInCF b) {
                // Thrown by NoElementQualifierHierarchy::isSubtype if qualifier
                // is not an exclusivity annotation. Can be ignored.
            }
        }
        return null;
    }

    public void useIFlowAfter(@NonNull Tree useIFlowAfter) {
        this.useIFlowAfter = useIFlowAfter;
    }

    public void useRegularIFlow() {
        this.useIFlowAfter = null;
    }

    @Override
    public @Nullable ExclusivityValue getInferredValueFor(Tree tree) {
        if (useIFlowAfter != null) {
            Tree oldUseIFlowAfter = useIFlowAfter;
            // getStoreAfter needs to use the regular information flow
            useRegularIFlow();
            final ExclusivityStore store;
            if (oldUseIFlowAfter instanceof VariableTree) {
                ExclusivityStore s = null;
                for (Node n : flowResult.getNodesForTree(oldUseIFlowAfter)) {
                    if (n instanceof AssignmentNode) {
                        s = flowResult.getStoreAfter(n);
                        break;
                    }
                }
                store = s;
            } else {
                store = flowResult.getStoreAfter(oldUseIFlowAfter);
            }
            Set<Node> nodes = flowResult.getNodesForTree(tree);
            useIFlowAfter(oldUseIFlowAfter);
            if (store == null || nodes == null) {
                return null;
            }

            return nodes.stream()
                    .map(node -> {
                        JavaExpression expr;
                        if (node instanceof ValueLiteralNode
                                || node instanceof BinaryOperationNode
                                || node instanceof UnaryOperationNode) {
                            return analysis.createAbstractValue(AnnotationMirrorSet.singleton(getDefaultPrimitiveQualifier()), node.getType());
                        } else if (!((expr = JavaExpression.fromNode(node)) instanceof Unknown)) {
                            return store.getValue(expr);
                        } else if (node instanceof MethodInvocationNode) {
                            return store.getValue((MethodInvocationNode) node);
                        } else if (node instanceof FieldAccessNode) {
                            return store.getValue((FieldAccessNode) node);
                        } else if (node instanceof ArrayAccessNode) {
                            return store.getValue((ArrayAccessNode) node);
                        } else if (node instanceof LocalVariableNode) {
                            return store.getValue((LocalVariableNode) node);
                        } else if (node instanceof ThisNode) {
                            return store.getValue((ThisNode) node);
                        } else {
                            return null;  // No refined value available
                        }})
                    .filter(Objects::nonNull)
                    .reduce(ExclusivityValue::leastUpperBound)
                    .orElse(null);
        } else {
            return super.getInferredValueFor(tree);
        }
    }

    public AnnotationMirror getExclusivityAnnotation(AnnotatedTypeMirror annotatedTypeMirror) {
        return annotatedTypeMirror.getAnnotationInHierarchy(READ_ONLY);
    }

    public AnnotationMirror getExclusivityAnnotation(Node node) {
        return getExclusivityAnnotation(getAnnotatedType(node.getTree()));
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(2);
        treeAnnotators.add(new ExclusivityPropagationTreeAnnotator(this));
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected ExclusivityViewpointAdapter createViewpointAdapter() {
        return new ExclusivityViewpointAdapter(this);
    }
}
