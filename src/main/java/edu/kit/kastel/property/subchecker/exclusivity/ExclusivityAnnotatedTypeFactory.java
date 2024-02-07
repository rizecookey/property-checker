package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import edu.kit.kastel.property.packing.PackingClientAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessTreeAnnotator;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.framework.flow.*;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Set;

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
        treeAnnotators.add(new ExclusivityTreeAnnotator(this));
        treeAnnotators.add(new PackingFieldAccessTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    private class ExclusivityTreeAnnotator extends TreeAnnotator {
        protected ExclusivityTreeAnnotator(AnnotatedTypeFactory aTypeFactory) {
            super(aTypeFactory);
        }

        @Override
        public Void visitNewClass(NewClassTree node, AnnotatedTypeMirror annotatedTypeMirror) {
            // new C() is always @ExclMut
            annotatedTypeMirror.replaceAnnotation(UNIQUE);
            return super.visitNewClass(node, annotatedTypeMirror);
        }
    }

    @Override
    protected ExclusivityViewpointAdapter createViewpointAdapter() {
        return new ExclusivityViewpointAdapter(this);
    }
}
