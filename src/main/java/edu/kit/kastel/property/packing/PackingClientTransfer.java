package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.ThisReference;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFAbstractTransfer;
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
                insertFieldsUpToFrame(initStore, receiverType, receiverPackingType, true);
            }
        }

        return initStore;
    }

    protected void insertFieldsUpToFrame(S store, AnnotatedTypeMirror receiverType, AnnotatedTypeMirror receiverPackingType, boolean removeUncommitted) {
        var factory = getAnalysis().getTypeFactory();
        PackingFieldAccessAnnotatedTypeFactory packingFactory =
                factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
        List<VariableElement> allFields = ElementUtils.getAllFieldsIn(
                TypesUtils.getTypeElement(receiverType.getUnderlyingType()),
                factory.getElementUtils());
        for (VariableElement field : allFields) {
            if (!ElementUtils.isStatic(field)) {
                ((PackingClientAnalysis<V, S, T>) analysis).setPosition(field);
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


                if (!packingFactory.isInitializedForFrame(receiverPackingType, fieldOwnerType)
                        && (!adaptedType.getKind().isPrimitive() || uncommitPrimitiveFields())) {
                    if (store.getValue(fieldAccess) == null || removeUncommitted) {
                        // If field is not initialized and not in store yet or uncommitted field values
                        // should be removed, insert the top value
                        adaptedType.clearAnnotations();
                        adaptedType.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
                        V value = analysis.createAbstractValue(adaptedType);
                        store.insertValue(fieldAccess, value);
                    }
                } else {
                    // if field is initialized, insert its declared type
                    V value = analysis.createAbstractValue(adaptedType);
                    store.insertValue(fieldAccess, value);
                }
            }
        }

    }

    protected abstract boolean uncommitPrimitiveFields();

    @Override
    protected void processPostconditions(Node invocationNode, S store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        ContractsFromMethod contractsUtils = analysis.getTypeFactory().getContractsFromMethod();
        Set<Contract.Postcondition> postconditions = contractsUtils.getPostconditions(executableElement);

        StringToJavaExpression stringToJavaExpr;

        if (invocationNode instanceof MethodInvocationNode mi) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atMethodInvocation(
                                    stringExpr,
                                    mi,
                                    analysis.getTypeFactory().getChecker());

            // Set receiver output type to input type by default.
            Node receiver = mi.getTarget().getReceiver();
            var method = analysis.getTypeFactory().methodFromUse(mi.getTree());
            AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();

            if (receiverType != null) {
                insertIfNotPresent(store, receiver, receiverType);
            }

            // Set parameter output types to input type by default.
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                insertIfNotPresent(store, mi.getArgument(i), paramType);
                ++i;
            }
        } else if (invocationNode instanceof ObjectCreationNode oc) {
            stringToJavaExpr =
                    stringExpr ->
                            StringToJavaExpression.atConstructorInvocation(
                                    stringExpr, oc.getTree(), analysis.getTypeFactory().getChecker());

            // Set parameter output types to input type by default.
            var method = analysis.getTypeFactory().constructorFromUse(oc.getTree());
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                insertIfNotPresent(store, oc.getArgument(i), paramType);
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
            AnnotationMirror anno = p.viewpointAdaptDependentTypeAnnotation(analysis.getTypeFactory(), stringToJavaExpr, null);

            String expressionString = p.expressionString;
            try {
                JavaExpression je = stringToJavaExpr.toJavaExpression(expressionString);
                // Unlike the superclass implementation, this calls
                // "insertValue" which for our type system replaces existing information instead of adding to it.
                // This is done because we use postconditions to implement output types for the parameters, which may
                // be incompatible with the input types. If a parameter has no explicit output type, we use its input
                // type as default, which is implemented above.
                store.insertValue(je, anno);
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
     * Inserts the given {@code type} for the {@code argument} expression if there isn't already a value
     * for that expression in the {@code store} that is more specific than a top type.
     *
     * @param store    store
     * @param argument expression node
     * @param type     type to insert
     */
    private void insertIfNotPresent(PackingClientStore<V, S> store, Node argument, AnnotatedTypeMirror type) {
        var expr = JavaExpression.fromNode(argument);
        if (!CFAbstractStore.canInsertJavaExpression(expr)) {
            return;
        }

        var hierarchy = analysis.getTypeFactory().getQualifierHierarchy();
        var top = hierarchy.getTopAnnotations().first();

        V existingVal = store.getValue(expr);

        if (existingVal == null
                || hierarchy.isSubtypeQualifiersOnly(top,
                hierarchy.findAnnotationInHierarchy(existingVal.getAnnotations(), top))) {
            V newVal = analysis.createAbstractValue(type);
            store.insertValue(expr, newVal);
        }

    }
}
