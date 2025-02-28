package edu.kit.kastel.property.subchecker.nullness;

import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodTree;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.lattice.SubAnnotationRelation;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.packing.PackingFieldAccessTreeAnnotator;
import edu.kit.kastel.property.subchecker.lattice.CooperativeAnnotatedTypeFactory;
import org.checkerframework.checker.nullness.*;
import org.checkerframework.checker.nullness.qual.NonNull;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.Pair;

import javax.lang.model.element.Element;
import javax.lang.model.type.TypeMirror;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class NullnessLatticeAnnotatedTypeFactory extends NullnessNoInitAnnotatedTypeFactory implements CooperativeAnnotatedTypeFactory {

    private Lattice lattice;

    /**
     * Creates a NullnessAnnotatedTypeFactory.
     *
     * @param checker the associated {@link NullnessNoInitSubchecker}
     */
    public NullnessLatticeAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit = true;

        Map<String, PropertyAnnotationType> annotationTypes = new HashMap<>();
        Map<Pair<String, String>, SubAnnotationRelation> relations = new HashMap<>();
        PropertyAnnotationType nonNull = new PropertyAnnotationType(NonNull.class, null, List.of(), "§subject§ != null", "true");
        PropertyAnnotationType nullable = new PropertyAnnotationType(Nullable.class, null, List.of(), "true", "true");
        annotationTypes.put("NonNull", nonNull);
        annotationTypes.put("Nullable", nullable);
        relations.put(
                Pair.of("NonNull", "Nullable"),
                new SubAnnotationRelation(new PropertyAnnotation(nonNull, List.of()), new PropertyAnnotation(nullable, List.of()), "true"));

        this.lattice = new Lattice(this, "nullness", annotationTypes, relations, Map.of(), Map.of());

        setCheckerMethods(
                lattice.getAnnotationTypes().values().stream()
                        .map(PropertyAnnotationType::getWellFormednessCheckable)
                        .collect(Collectors.toList()),
                Config.CHECKERS_CLASS_WELL_FORMEDNESS,
                Config::methodWellFormedness);

        setCheckerMethods(
                lattice.getAnnotationTypes().values().stream()
                        .map(PropertyAnnotationType::getPropertyCheckable)
                        .collect(Collectors.toList()),
                Config.CHECKERS_CLASS_PROPERTIES,
                Config::methodProperties);

        setCheckerMethods(
                new ArrayList<>(lattice.getRelations().values()),
                Config.CHECKERS_CLASS_RELATIONS,
                Config::methodRelations);

        postInit();
    }

    // Don't run postInit when it's called from the superclass.
    private boolean postInit = false;
    @Override
    protected void postInit() {
        if (!postInit) {
            postInit = true;
            return;
        }
        super.postInit();
    }

    @Override
    public NullnessLatticeSubchecker getChecker() {
        return (NullnessLatticeSubchecker) super.getChecker();
    }

    public Lattice getLattice() {
        return lattice;
    }

    @Override
    public NullnessNoInitTransfer createFlowTransferFunction(CFAbstractAnalysis<NullnessNoInitValue, NullnessNoInitStore, NullnessNoInitTransfer> analysis) {
        return new NullnessLatticeTransfer((NullnessNoInitAnalysis) analysis);
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        // Don't call super.createTreeAnnotator because the default tree annotators are incorrect
        // for the Nullness Checker.
        List<TreeAnnotator> annotators = new ArrayList<>(3);
        // annotators.add(new DebugListTreeAnnotator(new Tree.Kind[]
        // {Tree.Kind.CONDITIONAL_EXPRESSION}));
        annotators.add(new PackingFieldAccessTreeAnnotator(this));
        annotators.add(new NullnessPropagationTreeAnnotator(this));
        annotators.add(new LiteralTreeAnnotator(this));
        return new ListTreeAnnotator(annotators);
    }

    @Override
    public boolean isNotFullyInitializedReceiver(MethodTree methodDeclTree) {
        PackingFieldAccessAnnotatedTypeFactory initFactory =
                getChecker()
                        .getTypeFactoryOfSubcheckerOrNull(
                                PackingFieldAccessSubchecker.class);
        if (initFactory == null) {
            // init checker is deactivated.
            return super.isNotFullyInitializedReceiver(methodDeclTree);
        }
        return initFactory.isNotFullyInitializedReceiver(methodDeclTree);
    }

    @Override
    public AnnotatedTypeMirror getAnnotatedTypeBefore(JavaExpression expr, ExpressionTree tree) {
        PackingFieldAccessAnnotatedTypeFactory initFactory =
                getChecker()
                        .getTypeFactoryOfSubcheckerOrNull(
                                PackingFieldAccessSubchecker.class);
        if (initFactory == null) {
            // init checker is deactivated.
            return super.getAnnotatedTypeBefore(expr, tree);
        }
        if (expr instanceof FieldAccess) {
            FieldAccess fa = (FieldAccess) expr;
            JavaExpression receiver = fa.getReceiver();
            TypeMirror declaringClass = fa.getField().getEnclosingElement().asType();
            AnnotatedTypeMirror receiverType;

            if (receiver instanceof LocalVariable) {
                Element receiverElem = ((LocalVariable) receiver).getElement();
                receiverType = initFactory.getAnnotatedType(receiverElem);
            } else if (receiver instanceof ThisReference) {
                receiverType = initFactory.getSelfType(tree);
            } else {
                return super.getAnnotatedTypeBefore(expr, tree);
            }

            if (initFactory.isInitializedForFrame(receiverType, declaringClass)) {
                AnnotatedTypeMirror declared = getAnnotatedType(fa.getField());
                AnnotatedTypeMirror refined = super.getAnnotatedTypeBefore(expr, tree);
                AnnotatedTypeMirror res = AnnotatedTypeMirror.createType(fa.getType(), this, false);
                // If the expression is initialized, then by definition, it has at least its
                // declared annotation.
                // Assuming the correctness of the Nullness Checker's type refinement,
                // it also has its refined annotation.
                // We thus use the GLB of those two annotations.
                res.addAnnotations(
                        qualHierarchy.greatestLowerBoundsShallow(
                                declared.getAnnotations(),
                                declared.getUnderlyingType(),
                                refined.getAnnotations(),
                                refined.getUnderlyingType()));
                return res;
            }
        }

        // Is there anything better we could do?
        // Ideally, we would turn the expression string into a Tree or Element
        // instead of a JavaExpression, so we could use
        // atypeFactory.getAnnotatedType on the whole expression,
        // but that doesn't seem possible.
        return super.getAnnotatedTypeBefore(expr, tree);
    }

}
