package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityTransfer;
import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.MethodCall;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractTransfer;
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
        ((PackingClientAnalysis<?, ?, ?>) analysis).setPosition(underlyingAST.getCode());
        S initStore = super.initialStore(underlyingAST, parameters);
        PackingClientAnnotatedTypeFactory<?, ?, ?, ?> factory = getAnalysis().getTypeFactory();

        if (underlyingAST.getKind() == UnderlyingAST.Kind.METHOD) {
            // Add receiver value
            UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
            MethodTree methodDeclTree = method.getMethod();
            V initialThisValue = null;
            if (TreeUtils.isConstructor(methodDeclTree) || methodDeclTree.getReceiverParameter() != null) {
                initialThisValue = initialThisValue(methodDeclTree);
                initStore.initializeThisValue(initialThisValue);
            }

            if (!ElementUtils.isStatic(TreeUtils.elementFromDeclaration(methodDeclTree))) {
                // add fields declared in this class and all superclasses to store
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                AnnotatedTypeMirror receiverType =
                        factory.getSelfType(methodDeclTree.getBody());
                if (initialThisValue != null) {
                    receiverType.replaceAnnotations(initStore.getValue((ThisNode) null).getAnnotations());
                }

                AnnotatedTypeMirror receiverPackingType =
                        packingFactory.getSelfType(methodDeclTree.getBody());
                insertFieldsUpToFrame(initStore, receiverType, receiverPackingType);
            }
        }

        return initStore;
    }

    protected void insertFieldsUpToFrame(S store, AnnotatedTypeMirror receiverType, AnnotatedTypeMirror receiverPackingType) {
        var factory = getAnalysis().getTypeFactory();
        PackingFieldAccessAnnotatedTypeFactory packingFactory =
                factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
        List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                TypesUtils.getTypeElement(receiverType.getUnderlyingType()),
                factory.getElementUtils());
        for (VariableElement field : allFields) {
            if (!ElementUtils.isStatic(field)) {
                ((PackingClientAnalysis<V, S, T>) analysis).setPosition(factory.declarationFromElement(field));
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

                // Use top type if receiver is not sufficiently packed
                if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)
                        && (!adaptedType.getKind().isPrimitive() || uncommitPrimitiveFields())) {
                    adaptedType.clearAnnotations();
                    adaptedType.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
                }

                V value = analysis.createAbstractValue(adaptedType);
                store.insertValue(fieldAccess, value);
            }
        }

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

        AnnotationMirror top = analysis.getTypeFactory().getQualifierHierarchy().getTopAnnotations().first();
        MethodCall invocation;
        boolean sideEffectFree;
        StringToJavaExpression stringToJavaExpr = null;
        if (invocationNode instanceof MethodInvocationNode mi) {
            invocation = (MethodCall) JavaExpression.fromTree(mi.getTree());
            sideEffectFree = analysis.getTypeFactory().isSideEffectFree(mi.getTarget().getMethod());
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    mi,
                                    analysis.getTypeFactory().getChecker());

            // Set receiver output type to input type by default (unless receiver is @ReadOnly).
            Node receiver = mi.getTarget().getReceiver();

            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse(mi.getTree());
            AnnotatedTypeFactory.ParameterizedExecutableType exclMethod =
                    exclFactory.methodFromUse(mi.getTree());
            AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
            AnnotatedTypeMirror exclReceiverType = exclMethod.executableType.getReceiverType();


            if (receiverType != null && !exclReceiverType.hasAnnotation(ReadOnly.class)) {
                AnnotationMirror anno = receiverType.getAnnotationInHierarchy(top);
                V receiverValue = createPostconditionValue(anno, receiver.getType(), "this", invocation);
                V receiverDefaultValue = analysis.createAbstractValue(
                        receiverType.getAnnotations(),
                        receiverType.getUnderlyingType());

                JavaExpression receiverExpr = JavaExpression.fromNode(receiver);
                if (receiverValue != null) {
                    store.insertValue(receiverExpr, receiverValue);
                } else if (sideEffectFree) {
                    store.insertOrRefine(receiverExpr, receiverDefaultValue.getAnnotations().first());
                } else {
                    store.insertValue(receiverExpr, receiverDefaultValue);
                }
            }

            // Set parameter output types to input type by default (unless param is @ReadOnly or primitive).
            int i = 0;
            List<AnnotatedTypeMirror> exclParamTypes = exclMethod.executableType.getParameterTypes();
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                boolean paramReadOnly = exclParamTypes.get(i).hasAnnotation(ReadOnly.class);
                if (!paramReadOnly && ! paramType.getKind().isPrimitive()) {
                    V paramDefaultValue = analysis.createAbstractValue(
                            paramType.getAnnotations(),
                            paramType.getUnderlyingType());
                    V paramValue = createPostconditionValue(
                            paramType.getAnnotationInHierarchy(top), paramType.getUnderlyingType(),
                            method.executableType.getElement().getParameters().get(i).getSimpleName().toString(),
                            invocation
                    );
                    JavaExpression argument = JavaExpression.fromNode(mi.getArgument(i));
                    if (paramValue != null) {
                        store.insertValue(argument, paramValue);
                    } else if (sideEffectFree) {
                        store.insertOrRefine(argument, paramDefaultValue.getAnnotations().first());
                    } else {
                        store.insertValue(argument, paramDefaultValue);
                    }
                }

                ++i;
            }
        } else if (invocationNode instanceof ObjectCreationNode oc) {
            invocation = JavaExpressionUtil.constructorCall(oc.getTree());
            sideEffectFree = false;
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
                    JavaExpression argument = JavaExpression.fromNode(oc.getArgument(i));
                    V paramValue = createPostconditionValue(
                            paramType.getAnnotationInHierarchy(top), paramType.getUnderlyingType(),
                            method.executableType.getElement().getParameters().get(i).getSimpleName().toString(),
                            invocation
                    );
                    if (paramValue != null) {
                        store.insertValue(argument, paramValue);
                    } else {
                        store.insertValue(argument, paramDefaultValue);
                    }
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
            AnnotationMirror anno = p.annotation;

            String expressionString = p.expressionString;
            try {
                // TODO: parse with params as locals (StringToJavaExpression.atPath)
                JavaExpression je = stringToJavaExpr.toJavaExpression(expressionString);

                // Unlike the superclass implementation, this calls
                // "insertValue" which for our type system replaces existing information instead of adding to it.
                // This is done because we use postconditions to implement output types for the parameters, which may
                // be incompatible with the input types. If a parameter has no explicit output type, we use its input
                // type as default, which is implemented above.
                V newValue = createPostconditionValue(anno, je.getType(), expressionString, invocation);
                if (newValue != null) {
                    store.insertValue(je, newValue);
                } else if (sideEffectFree) {
                    store.insertOrRefine(je, anno);
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

    /**
     * Optional method to compute a custom post condition type value. If this method returns {@code null}, the default
     * behaviour is chosen instead, which is to either insert the annotation into the store or use the annotation to
     * refine the existing value for the subject if the method in question is side-effect free.
     *
     * @param annotation type annotation the post condition refers to
     * @param subjectType subject base type.
     * @param subject subject expression (not viewpoint-adapted)
     * @param invocation method/constructor invocation
     * @return a value or {@code null}
     */
    protected @Nullable V createPostconditionValue(
            AnnotationMirror annotation,
            TypeMirror subjectType,
            String subject,
            MethodCall invocation
    ) {
        return null;
    }
}
