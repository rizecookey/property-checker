package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.MethodTree;

import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import edu.kit.kastel.property.subchecker.exclusivity.rules.*;

import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.AnnotatedTypes;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;

public class ExclusivityTransfer extends CFTransfer {
    private final ExclusivityAnnotatedTypeFactory factory;

    public ExclusivityTransfer(CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis,
                               ExclusivityAnnotatedTypeFactory factory) {
        super(analysis);
        assert factory == analysis.getTypeFactory();
        this.factory = factory;
    }

    @Override
    public TransferResult<CFValue, CFStore> visitAssignment(
            AssignmentNode node, TransferInput<CFValue, CFStore> in) {
        CFStore store = in.getRegularStore();

        if (node.getExpression() instanceof MethodInvocationNode) {
            new TMethodInvocationHelper(store, factory, analysis)
                    .applyOrInvalidate(node.getTarget(), node.getExpression());
        } else {
            new TAssign(store, factory, analysis).applyOrInvalidate(node.getTarget(), node.getExpression());
        }

        return new RegularTransferResult<>(null, in.getRegularStore());
    }

    @Override
    public TransferResult<CFValue, CFStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<CFValue, CFStore> in
    ) {
        CFStore store = in.getRegularStore();

        try {
            new TMethodInvocation(store, factory, analysis).apply(n);
        } catch (RuleNotApplicable e) {
            new TInvalidate(store, factory, analysis).apply(n);
        }

        return new RegularTransferResult<>(null, store);
    }

    @Override
    public TransferResult<CFValue, CFStore> visitReturn(
            ReturnNode node, TransferInput<CFValue, CFStore> in) {
        CFStore store = in.getRegularStore();

        MethodTree methodTree = (MethodTree) factory.getEnclosingClassOrMethod(node.getTree());
        assert methodTree != null;
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(
                factory.getAnnotatedType(methodTree).getReturnType());

        new TAssign(store, factory, analysis).applyOrInvalidate(returnTypeAnno, node.getResult());

        return new RegularTransferResult<>(null, store);
    }

    @Override
    public CFStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        CFStore initStore = super.initialStore(underlyingAST, parameters);

        // Add receiver value
        UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
        MethodTree methodDeclTree = method.getMethod();
        if (methodDeclTree.getReceiverParameter() != null) {
            AnnotatedTypeMirror thisType = factory.getAnnotatedType(methodDeclTree.getReceiverParameter());
            initStore.initializeThisValue(thisType.getAnnotationInHierarchy(
                            AnnotationBuilder.fromClass(factory.getElementUtils(), Unique.class)),
                    thisType.getUnderlyingType());
        }

        // The default implementation only adds fields declared in this class.
        // To make type-checking of pack statements more precise, we also add all fields declared in superclasses.
        if (underlyingAST.getKind() == UnderlyingAST.Kind.METHOD) {
            ExecutableElement methodElem = TreeUtils.elementFromDeclaration(methodDeclTree);
            ClassTree classTree = method.getClassTree();

            if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                        TypesUtils.getTypeElement(((JCTree) classTree).type),
                        factory.getElementUtils());
                AnnotatedTypeMirror receiverType =
                        factory.getSelfType(methodDeclTree.getBody());

                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                AnnotatedTypeMirror receiverPackingType =
                        packingFactory.getSelfType(methodDeclTree.getBody());

                for (VariableElement field : allFields) {
                    if (!ElementUtils.isStatic(field)) {
                        FieldAccess fieldAccess = new FieldAccess(new ThisReference(methodElem.getReceiverType()), field);
                        TypeMirror fieldOwnerType = field.getEnclosingElement().asType();
                        AnnotatedTypeMirror declaredType = factory.getAnnotatedType(field);

                        // Viewpoint-adapt type
                        AnnotatedTypeMirror adaptedType =
                                AnnotatedTypes.asMemberOf(
                                        analysis.getTypes(),
                                        analysis.getTypeFactory(),
                                        receiverType,
                                        field,
                                        declaredType);

                        if (adaptedType == null) {
                            adaptedType = declaredType;
                        }

                        // Use @ReadOnly if receiver is not sufficiently packed
                        if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)) {
                            adaptedType.clearAnnotations();
                            adaptedType.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
                        }

                        CFValue value = analysis.createAbstractValue(adaptedType);

                        initStore.insertValue(fieldAccess, value);
                    }
                }
            }
        }

        return initStore;
    }
}
