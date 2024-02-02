package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

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
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.*;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.*;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Set;

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
        if (!TreeUtils.isConstructor(methodDeclTree) && methodDeclTree.getReceiverParameter() != null) {
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

    @Override
    protected void processPostconditions(Node invocationNode, ExclusivityStore store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        ContractsFromMethod contractsUtils = analysis.getTypeFactory().getContractsFromMethod();
        Set<Contract.Postcondition> postconditions = contractsUtils.getPostconditions(executableElement);

        StringToJavaExpression stringToJavaExpr = null;
        if (invocationNode instanceof MethodInvocationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    (MethodInvocationNode) invocationNode,
                                    analysis.getTypeFactory().getChecker());

            // Set receiver output type to input type by default.
            Node receiver = ((MethodInvocationNode) invocationNode).getTarget().getReceiver();

            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse((MethodInvocationTree) invocationNode.getTree());
            AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
            if (receiverType != null) {
                ExclusivityValue receiverDefaultValue = new ExclusivityValue(
                        getAnalysis(),
                        receiverType.getAnnotations(),
                        receiverType.getUnderlyingType());
                store.insertValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
            }

            // Set parameter output types to input type by default.
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                ExclusivityValue paramDefaultValue = new ExclusivityValue(
                        getAnalysis(),
                        paramType.getAnnotations(),
                        paramType.getUnderlyingType());
                store.insertValue(
                        JavaExpression.fromNode(((MethodInvocationNode) invocationNode).getArgument(i++)),
                        paramDefaultValue);
            }
        } else if (invocationNode instanceof ObjectCreationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atConstructorInvocation(
                                    stringExpr, (NewClassTree) invocationTree, analysis.getTypeFactory().getChecker());

            // Set parameter output types to input type by default.
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().constructorFromUse((NewClassTree) invocationNode.getTree());
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                ExclusivityValue paramDefaultValue = new ExclusivityValue(
                        getAnalysis(),
                        paramType.getAnnotations(),
                        paramType.getUnderlyingType());
                store.insertValue(
                        JavaExpression.fromNode(((ObjectCreationNode) invocationNode).getArgument(i++)),
                        paramDefaultValue);
            }
        } else {
            throw new BugInCF(
                    "CFAbstractTransfer.processPostconditionsAndConditionalPostconditions"
                            + " expects a MethodInvocationNode or ObjectCreationNode argument;"
                            + " received a "
                            + invocationNode.getClass().getSimpleName());
        }

        for (Contract p : postconditions) {
            // Viewpoint-adapt to the method use (the call site).
            AnnotationMirror anno =
                    p.viewpointAdaptDependentTypeAnnotation(
                            analysis.getTypeFactory(), stringToJavaExpr, /* errorTree= */ null);

            String expressionString = p.expressionString;
            try {
                JavaExpression je = stringToJavaExpr.toJavaExpression(expressionString);

                // Unlike the superclass implementation, this calls
                // "insertValue" which for our type system replaces existing information instead of adding to it.
                // This is done because we use postconditions to implement output types for the parameters, which may
                // be incompatible with the input types. If a parameter has no explicit output type, we use its input
                // type as default, which is implemented above.
                if (p.kind == Contract.Kind.CONDITIONALPOSTCONDITION) {
                    store.insertValue(je, anno);
                } else {
                    store.insertValue(je, anno);
                }
            } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                // report errors here
                if (e.isFlowParseError()) {
                    Object[] args = new Object[e.args.length + 1];
                    args[0] =
                            ElementUtils.getSimpleSignature(
                                    (ExecutableElement) TreeUtils.elementFromUse(invocationTree));
                    System.arraycopy(e.args, 0, args, 1, e.args.length);
                    analysis.getTypeFactory().getChecker().reportError(
                            invocationTree, "flowexpr.parse.error.postcondition", args);
                } else {
                    analysis.getTypeFactory().getChecker().report(invocationTree, e.getDiagMessage());
                }
            }
        }
    }
}
