package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import edu.kit.kastel.property.subchecker.exclusivity.qual.Unique;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractTransfer;
import org.checkerframework.framework.flow.CFAbstractValue;
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

public abstract class PackingClientTransfer<
        V extends PackingClientValue<V>,
        S extends PackingClientStore<V, S>,
        T extends PackingClientTransfer<V, S, T>>
        extends CFAbstractTransfer<V, S, T> {

    protected PackingClientTransfer(CFAbstractAnalysis<V, S, T> analysis) {
        super(analysis);
    }

    protected PackingClientTransfer(CFAbstractAnalysis<V, S, T> analysis, boolean forceConcurrentSemantics) {
        super(analysis, forceConcurrentSemantics);
    }

    public PackingClientAnalysis getAnalysis() {
        return (PackingClientAnalysis) analysis;
    }

    protected abstract V initialThisValue(MethodTree methodDeclTree);

    @Override
    public S initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        S initStore = super.initialStore(underlyingAST, parameters);
        PackingClientAnnotatedTypeFactory factory = getAnalysis().getTypeFactory();

        if (underlyingAST.getKind() == UnderlyingAST.Kind.METHOD) {
            // Add receiver value

            UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
            MethodTree methodDeclTree = method.getMethod();
            V initialThisValue = null;
            if (TreeUtils.isConstructor(methodDeclTree) || methodDeclTree.getReceiverParameter() != null) {
                initialThisValue = initialThisValue(methodDeclTree);
                initStore.initializeThisValue(initialThisValue);
            }

            // The default implementation only adds fields declared in this class.
            // To make type-checking of pack statements more precise, we also add all fields declared in superclasses.
            ClassTree classTree = method.getClassTree();

            if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                        TypesUtils.getTypeElement(((JCTree) classTree).type),
                        factory.getElementUtils());
                AnnotatedTypeMirror receiverType =
                        factory.getSelfType(methodDeclTree.getBody());
                if (initialThisValue != null) {
                    receiverType.replaceAnnotations(initStore.getValue((ThisNode) null).getAnnotations());
                }

                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                AnnotatedTypeMirror receiverPackingType =
                        packingFactory.getSelfType(methodDeclTree.getBody());

                for (VariableElement field : allFields) {
                    if (!ElementUtils.isStatic(field)) {
                        FieldAccess fieldAccess = new FieldAccess(new ThisReference(receiverType.getUnderlyingType()), field);
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
                        if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)
                                && (!adaptedType.getKind().isPrimitive() || uncommitPrimitiveFields())) {
                            adaptedType.clearAnnotations();
                            adaptedType.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
                        }

                        V value = analysis.createAbstractValue(adaptedType);

                        initStore.insertValue(fieldAccess, value);
                    }
                }
            }
        }

        return initStore;
    }

    protected abstract boolean uncommitPrimitiveFields();

    @Override
    protected void processPostconditions(Node invocationNode, S store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        ContractsFromMethod contractsUtils = analysis.getTypeFactory().getContractsFromMethod();
        Set<Contract.Postcondition> postconditions = contractsUtils.getPostconditions(executableElement);
        ExclusivityAnnotatedTypeFactory exclFactory;
        if (this instanceof ExclusivityTransfer) {
            exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory();
        } else {
            exclFactory = analysis.getTypeFactory().getTypeFactoryOfSubchecker(ExclusivityChecker.class);
        }

        StringToJavaExpression stringToJavaExpr = null;
        if (invocationNode instanceof MethodInvocationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    (MethodInvocationNode) invocationNode,
                                    analysis.getTypeFactory().getChecker());

            // Set receiver output type to input type by default (unless receiver is @ReadOnly).
            Node receiver = ((MethodInvocationNode) invocationNode).getTarget().getReceiver();

            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse((MethodInvocationTree) invocationNode.getTree());
            AnnotatedTypeFactory.ParameterizedExecutableType exclMethod =
                    exclFactory.methodFromUse((MethodInvocationTree) invocationNode.getTree());
            AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
            AnnotatedTypeMirror exclReceiverType = exclMethod.executableType.getReceiverType();

            if (receiverType != null && !exclReceiverType.hasAnnotation(ReadOnly.class)) {
                V receiverDefaultValue = analysis.createAbstractValue(
                        receiverType.getAnnotations(),
                        receiverType.getUnderlyingType());
                store.insertValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
            }

            // Set parameter output types to input type by default (unless param is @ReadOnly).
            int i = 0;
            List<AnnotatedTypeMirror> exclParamTypes = exclMethod.executableType.getParameterTypes();
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                boolean paramReadOnly = exclParamTypes.get(i).hasAnnotation(ReadOnly.class);
                if (!paramReadOnly) {
                    V paramDefaultValue = analysis.createAbstractValue(
                            paramType.getAnnotations(),
                            paramType.getUnderlyingType());
                    store.insertValue(
                            JavaExpression.fromNode(((MethodInvocationNode) invocationNode).getArgument(i)),
                            paramDefaultValue);
                }

                ++i;
            }
        } else if (invocationNode instanceof ObjectCreationNode) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atConstructorInvocation(
                                    stringExpr, (NewClassTree) invocationTree, analysis.getTypeFactory().getChecker());

            // Set parameter output types to input type by default.
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().constructorFromUse((NewClassTree) invocationNode.getTree());
            AnnotatedTypeFactory.ParameterizedExecutableType exclMethod =
                    exclFactory.constructorFromUse((NewClassTree) invocationNode.getTree());
            int i = 0;
            List<AnnotatedTypeMirror> exclParamTypes = exclMethod.executableType.getParameterTypes();
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                boolean paramReadOnly = exclParamTypes.get(i).hasAnnotation(ReadOnly.class);
                if (!paramReadOnly) {
                    V paramDefaultValue = analysis.createAbstractValue(
                            paramType.getAnnotations(),
                            paramType.getUnderlyingType());
                    store.insertValue(
                            JavaExpression.fromNode(((ObjectCreationNode) invocationNode).getArgument(i)),
                            paramDefaultValue);
                }

                ++i;
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
