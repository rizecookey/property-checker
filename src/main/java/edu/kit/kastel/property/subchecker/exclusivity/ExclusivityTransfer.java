package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.ClassTree;
import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodTree;

import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import edu.kit.kastel.property.subchecker.exclusivity.rules.*;

import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.*;
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

public class ExclusivityTransfer extends CFAbstractTransfer<ExclusivityValue, ExclusivityStore, ExclusivityTransfer> {

    private final ExclusivityAnnotatedTypeFactory factory;

    public ExclusivityTransfer(ExclusivityAnalysis analysis,
                               ExclusivityAnnotatedTypeFactory factory) {
        super(analysis);
        assert factory == analysis.getTypeFactory();
        this.factory = factory;
    }

    public ExclusivityAnalysis getAnalysis() {
        return (ExclusivityAnalysis) analysis;
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitAssignment(
            AssignmentNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        if (node.getExpression() instanceof MethodInvocationNode) {
            new TMethodInvocationHelper(store, factory, getAnalysis())
                    .applyOrInvalidate(node.getTarget(), node.getExpression());
        } else {
            new TAssign(store, factory, getAnalysis()).applyOrInvalidate(node.getTarget(), node.getExpression());
        }

        return new RegularTransferResult<>(null, in.getRegularStore());
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<ExclusivityValue, ExclusivityStore> in
    ) {
        ExclusivityStore store = in.getRegularStore();
        ExpressionTree invocationTree = n.getTree();
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();

        if (receiver instanceof ClassNameNode && ((ClassNameNode) receiver).getElement().toString().equals(Packing.class.getName())) {
            // Packing statements don't change the store
            return new RegularTransferResult<>(null, store, false);
        }

        try {
            new TMethodInvocation(store, factory, getAnalysis()).apply(n);
        } catch (RuleNotApplicable e) {
            new TInvalidate(store, factory, getAnalysis()).apply(n);
        }

        processPostconditions(n, store, method, invocationTree);

        return new RegularTransferResult<>(null, store, true);
    }

    @Override
    public TransferResult<ExclusivityValue, ExclusivityStore> visitReturn(
            ReturnNode node, TransferInput<ExclusivityValue, ExclusivityStore> in) {
        ExclusivityStore store = in.getRegularStore();

        MethodTree methodTree = (MethodTree) factory.getEnclosingClassOrMethod(node.getTree());
        assert methodTree != null;
        AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(
                factory.getAnnotatedType(methodTree).getReturnType());



        new TAssign(store, factory, getAnalysis()).applyOrInvalidate(returnTypeAnno, node.getResult());

        return new RegularTransferResult<>(null, store);
    }

    @Override
    public ExclusivityStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        ExclusivityStore initStore = super.initialStore(underlyingAST, parameters);

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

                        ExclusivityValue value = analysis.createAbstractValue(adaptedType);

                        initStore.insertValue(fieldAccess, value);
                    }
                }
            }
        }

        return initStore;
    }
}
