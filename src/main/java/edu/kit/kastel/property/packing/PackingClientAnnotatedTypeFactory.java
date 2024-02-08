package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.Unknown;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractTransfer;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.PropagationTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.AnnotationMirrorSet;

import javax.lang.model.element.AnnotationMirror;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Set;

public abstract class PackingClientAnnotatedTypeFactory<
        Value extends CFAbstractValue<Value>,
        Store extends CFAbstractStore<Value, Store>,
        TransferFunction extends CFAbstractTransfer<Value, Store, TransferFunction>,
        FlowAnalysis extends CFAbstractAnalysis<Value, Store, TransferFunction>>
        extends GenericAnnotatedTypeFactory<Value, Store, TransferFunction, FlowAnalysis> {

    private boolean useInputTypeLhs;
    private @Nullable Tree useIFlowAfter;

    protected PackingClientAnnotatedTypeFactory(BaseTypeChecker checker, boolean useFlow) {
        super(checker, useFlow);
    }

    protected PackingClientAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
    }

    public void setUseInputTypeLhs(boolean useInputTypeLhs) {
        this.useInputTypeLhs = useInputTypeLhs;
    }

    @Override
    public AnnotatedTypeMirror getAnnotatedTypeLhs(Tree lhsTree) {
        AnnotatedTypeMirror annotatedType = super.getAnnotatedTypeLhs(lhsTree);

        if (!useInputTypeLhs) {
            Tree containingMethod = getEnclosingClassOrMethod(lhsTree);
            // For method parameters, the lhs type is always @ReadOnly
            if (lhsTree instanceof IdentifierTree && containingMethod instanceof MethodTree) {
                boolean isParam = ((IdentifierTree) lhsTree).getName().toString().equals("this");
                for (VariableTree param : ((MethodTree) containingMethod).getParameters()) {
                    isParam |= param.getName().equals(((IdentifierTree) lhsTree).getName());
                }

                if (isParam) {
                    annotatedType.replaceAnnotations(getQualifierHierarchy().getTopAnnotations());
                }
            }
        }

        return annotatedType;
    }

    @Override
    public AnnotationMirrorSet getExplicitNewClassAnnos(NewClassTree newClassTree) {
        // Return empty set so that the type visitor adds the annotation from the return type.
        return AnnotationMirrorSet.emptySet();
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(3);
        treeAnnotators.add(new PropagationTreeAnnotator(this));
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    public void useIFlowAfter(@NonNull Tree useIFlowAfter) {
        this.useIFlowAfter = useIFlowAfter;
    }

    public void useRegularIFlow() {
        this.useIFlowAfter = null;
    }

    public abstract AnnotationMirror getDefaultPrimitiveQualifier();

    @Override
    public AnnotatedTypeMirror.AnnotatedNullType getAnnotatedNullType(Set<? extends AnnotationMirror> annotations) {
        AnnotatedTypeMirror.AnnotatedNullType result = super.getAnnotatedNullType(annotations);
        result.replaceAnnotation(getDefaultPrimitiveQualifier());
        return result;
    }

    @Override
    public @Nullable Value getInferredValueFor(Tree tree) {
        if (useIFlowAfter != null) {
            Tree oldUseIFlowAfter = useIFlowAfter;
            // getStoreAfter needs to use the regular information flow
            useRegularIFlow();
            final Store store;
            if (oldUseIFlowAfter instanceof VariableTree) {
                Store s = null;
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
                    .reduce(Value::leastUpperBound)
                    .orElse(null);
        } else {
            return super.getInferredValueFor(tree);
        }
    }

    @Override
    protected void applyInferredAnnotations(AnnotatedTypeMirror type, Value inferred) {
        type.replaceAnnotations(inferred.getAnnotations());
    }

    @Override
    protected @Nullable CFGVisualizer<Value, Store, TransferFunction> createCFGVisualizer() {
        if (checker.hasOption("flowdotdir")) {
            try {
                Files.createDirectories(Path.of(checker.getOption("flowdotdir")));
            } catch (IOException e) { }
        }
        return super.createCFGVisualizer();
    }
}
