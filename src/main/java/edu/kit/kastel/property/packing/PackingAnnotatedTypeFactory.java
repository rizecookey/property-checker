package edu.kit.kastel.property.packing;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.NewClassTree;
import com.sun.source.tree.Tree;
import com.sun.source.util.TreePath;
import com.sun.tools.javac.tree.JCTree;
import org.checkerframework.checker.initialization.*;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractValue;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.treeannotator.ListTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.LiteralTreeAnnotator;
import org.checkerframework.framework.type.treeannotator.TreeAnnotator;
import org.checkerframework.framework.type.typeannotator.IrrelevantTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.ListTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.PropagationTypeAnnotator;
import org.checkerframework.framework.type.typeannotator.TypeAnnotator;
import org.checkerframework.framework.util.QualifierKind;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;

public class PackingAnnotatedTypeFactory
        extends InitializationAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    public PackingAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected @Nullable PackingFieldAccessAnnotatedTypeFactory getFieldAccessFactory() {
        return getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
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

        List<VariableElement> uninitializedFields =  getUninitializedFieldsForTarget(initStore, targetStore, path, isStatic, receiverAnnotations);

        getFieldAccessFactory().setComputingUninitializedFields(wasComputingUninitializedFields);
        return uninitializedFields;
    }

    private List<VariableElement> getUninitializedFieldsForTarget(
            PackingStore initStore,
            CFAbstractStore<?, ?> targetStore,
            TreePath path,
            boolean isStatic,
            Collection<? extends AnnotationMirror> receiverAnnotations) {
        List<VariableElement> uninitializedFields =
                getUninitializedFields(initStore, path, isStatic, receiverAnnotations);
        ClassTree currentClass = TreePathUtil.enclosingClass(path);

        PackingClientAnnotatedTypeFactory factory = ((PackingClientStore) targetStore).getFactory();

        if (factory == null) {
            throw new BugInCF(
                    "Did not find target type factory for checker "
                            + ((InitializationChecker) checker).getTargetCheckerClass());
        }

        // Remove primitives
        if (!((InitializationChecker) checker).checkPrimitives()) {
            uninitializedFields.removeIf(var -> getAnnotatedType(var).getKind().isPrimitive());
        }

        // Filter out fields which are initialized according to subchecker
        uninitializedFields.removeIf(
                field -> {
                    JavaExpression receiver;
                    if (ElementUtils.isStatic(field)) {
                        receiver = new ClassName(((JCTree) currentClass).type);
                    } else {
                        receiver = new ThisReference(((JCTree) currentClass).type);
                    }
                    FieldAccess fa = new FieldAccess(receiver, field);
                    CFAbstractValue<?> value = targetStore.getFieldValue(fa);
                    return isInitialized(factory, value, field);
                });

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
    public AnnotationMirrorSet getExplicitNewClassAnnos(NewClassTree newClassTree) {
        // Return empty set so that the type visitor adds the annotation from the return type.
        return AnnotationMirrorSet.emptySet();
    }

    @Override
    protected void setSelfTypeInInitializationCode(
            Tree tree, AnnotatedTypeMirror.AnnotatedDeclaredType selfType, TreePath path) {
        selfType.replaceAnnotation(createUnknownInitializationAnnotation(Object.class));
    }

    @Override
    public @Nullable CFValue getInferredValueFor(Tree tree) {
        final PackingStore store = flowResult.getStoreBefore(tree);
        Set<Node> nodes = flowResult.getNodesForTree(tree);

        if (store == null || nodes == null) {
            return null;
        }

        return nodes.stream()
                .map(node -> {
                    JavaExpression expr;
                    if (node instanceof ValueLiteralNode
                            || node instanceof BinaryOperationNode
                            || node instanceof UnaryOperationNode) {
                        return analysis.createAbstractValue(AnnotationMirrorSet.singleton(INITIALIZED), node.getType());
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
                .reduce(CFValue::leastUpperBound)
                .orElse(null);
    }

    @Override
    protected void applyInferredAnnotations(AnnotatedTypeMirror type, CFValue inferred) {
        type.replaceAnnotations(inferred.getAnnotations());
    }

    @Override
    protected TreeAnnotator createTreeAnnotator() {
        List<TreeAnnotator> treeAnnotators = new ArrayList<>(2);
        treeAnnotators.add(new LiteralTreeAnnotator(this).addStandardLiteralQualifiers());
        if (dependentTypesHelper.hasDependentAnnotations()) {
            treeAnnotators.add(dependentTypesHelper.createDependentTypesTreeAnnotator());
        }
        treeAnnotators.add(getFieldAccessFactory().new PackingTreeAnnotator(this));
        return new ListTreeAnnotator(treeAnnotators);
    }

    @Override
    protected TypeAnnotator createTypeAnnotator() {
        List<TypeAnnotator> typeAnnotators = new ArrayList<>(1);
        if (relevantJavaTypes != null) {
            typeAnnotators.add(new IrrelevantTypeAnnotator(this));
        }
        typeAnnotators.add(new PropagationTypeAnnotator(this));
        typeAnnotators.add(getFieldAccessFactory().new PackingTypeAnnotator(this));
        return new ListTypeAnnotator(typeAnnotators);
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
