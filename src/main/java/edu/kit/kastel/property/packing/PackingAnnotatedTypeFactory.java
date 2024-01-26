package edu.kit.kastel.property.packing;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.util.TypeUtils;
import org.checkerframework.checker.initialization.*;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.ClassNameNode;
import org.checkerframework.dataflow.cfg.node.FieldAccessNode;
import org.checkerframework.dataflow.cfg.node.ImplicitThisNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.QualifierKind;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.ElementFilter;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

public class PackingAnnotatedTypeFactory
        extends InitializationAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    public PackingAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected @Nullable PackingFieldAccessAnnotatedTypeFactory getFieldAccessFactory() {
        PackingChecker checker = getChecker();
        BaseTypeChecker targetChecker = checker.getSubchecker(checker.getTargetCheckerClass());
        return targetChecker.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }

    @Override
    public PackingChecker getChecker() {
        return (PackingChecker) super.getChecker();
    }

    @Override
    protected QualifierHierarchy createQualifierHierarchy() {
        return new PackingQualifierHierarchy();
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore initStore,
            CFAbstractStore<?, ?> targetStore,
            TreePath path, boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = getFieldAccessFactory().isComputingUninitializedFields();

        List<VariableElement> uninitializedFields =  super.getUninitializedFields(initStore, targetStore, path, isStatic, receiverAnnotations);

        getFieldAccessFactory().setComputingUninitializedFields(wasComputingUninitializedFields);
        return uninitializedFields;
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore store,
            TreePath path,
            boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = getFieldAccessFactory().isComputingUninitializedFields();
        getFieldAccessFactory().setComputingUninitializedFields(true);

        List<VariableElement> uninitializedFields = super.getUninitializedFields(store, path, isStatic, receiverAnnotations);

        getFieldAccessFactory().setComputingUninitializedFields(wasComputingUninitializedFields);
        return uninitializedFields;
    }

    @Override
    protected List<VariableElement> getPossiblyUninitializedFields(TreePath path) {
        ClassTree currentClass = TreePathUtil.enclosingClass(path);
        return ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(((JCTree) currentClass).type), elements);
    }

    @Override
    protected void setSelfTypeInInitializationCode(
            Tree tree, AnnotatedTypeMirror.AnnotatedDeclaredType selfType, TreePath path) {
        // TODO: For now, the packing checker only changes a reference's type for explicit (un-)pack statements.
        // When implementing implicit (un-)packing, remove this override.
        return;
    }

    protected AnnotationMirror getInitialized() {
        return INITIALIZED;
    }

    protected AnnotationMirror getUnknownInitialization() {
        return UNKNOWN_INITIALIZATION;
    }

    protected AnnotationMirror getUnderInitialization() {
        return UNDER_INITALIZATION;
    }

    protected AnnotationMirror getFBCBottom() {
        return FBCBOTTOM;
    }

    protected class PackingQualifierHierarchy extends InitializationQualifierHierarchy {

        /** Qualifier kind for the @{@link UnknownInitialization} annotation. */
        private final QualifierKind UNKNOWN_INIT;

        /** Qualifier kind for the @{@link UnderInitialization} annotation. */
        private final QualifierKind UNDER_INIT;

        /** Create an InitializationQualifierHierarchy. */
        protected PackingQualifierHierarchy() {
            UNKNOWN_INIT = getQualifierKind(UNKNOWN_INITIALIZATION);
            UNDER_INIT = getQualifierKind(UNDER_INITALIZATION);
        }

        @Override
        public boolean isSubtypeWithElements(
                AnnotationMirror subAnno,
                QualifierKind subKind,
                AnnotationMirror superAnno,
                QualifierKind superKind) {
            if (!subKind.isSubtypeOf(superKind)) {
                return false;
            } else if ((subKind == UNDER_INIT && superKind == UNDER_INIT)) {
                // TODO: Is it a good idea to redefine UNDER_INIT as invariant?
                // Probably better to define our own annotations.
                return AnnotationUtils.areSame(subAnno, superAnno);
            } else if ((subKind == UNDER_INIT && superKind == UNKNOWN_INIT)
                    || (subKind == UNKNOWN_INIT && superKind == UNKNOWN_INIT)) {
                TypeMirror frame1 = getTypeFrameFromAnnotation(subAnno);
                TypeMirror frame2 = getTypeFrameFromAnnotation(superAnno);
                return types.isSubtype(frame1, frame2);
            } else {
                return true;
            }
        }

        @Override
        protected AnnotationMirror leastUpperBoundWithElements(
                AnnotationMirror anno1,
                QualifierKind qual1,
                AnnotationMirror anno2,
                QualifierKind qual2,
                QualifierKind lubKind) {
            // Handle the case where one is a subtype of the other.
            if (isSubtypeWithElements(anno1, qual1, anno2, qual2)) {
                return anno2;
            } else if (isSubtypeWithElements(anno2, qual2, anno1, qual1)) {
                return anno1;
            }
            boolean unknowninit1 = isUnknownInitialization(anno1);
            boolean unknowninit2 = isUnknownInitialization(anno2);
            boolean underinit1 = isUnderInitialization(anno1);
            boolean underinit2 = isUnderInitialization(anno2);

            // Handle @Initialized.
            if (isInitialized(anno1)) {
                assert underinit2;
                return createUnknownInitializationAnnotation(getTypeFrameFromAnnotation(anno2));
            } else if (isInitialized(anno2)) {
                assert underinit1;
                return createUnknownInitializationAnnotation(getTypeFrameFromAnnotation(anno1));
            }

            if (underinit1 && underinit2) {
                return createUnknownInitializationAnnotation(
                        lubTypeFrame(
                                getTypeFrameFromAnnotation(anno1),
                                getTypeFrameFromAnnotation(anno2)));
            }

            assert (unknowninit1 || underinit1) && (unknowninit2 || underinit2);
            return createUnknownInitializationAnnotation(
                    lubTypeFrame(
                            getTypeFrameFromAnnotation(anno1), getTypeFrameFromAnnotation(anno2)));
        }
    }
}
