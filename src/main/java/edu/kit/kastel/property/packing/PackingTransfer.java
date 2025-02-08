package edu.kit.kastel.property.packing;

import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodInvocationTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.NewClassTree;
import com.sun.tools.javac.code.Symbol;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.initialization.InitializationAbstractTransfer;
import org.checkerframework.checker.initialization.qual.FBCBottom;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.UnderlyingAST;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeFactory;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.Contract;
import org.checkerframework.framework.util.ContractsFromMethod;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.*;
import javax.lang.model.type.TypeMirror;
import java.util.List;
import java.util.Set;

public class PackingTransfer extends InitializationAbstractTransfer<CFValue, PackingStore, PackingTransfer> {

    public PackingTransfer(PackingAnalysis analysis) {
        super(analysis);
    }

    @Override
    public PackingStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        PackingStore initStore = super.initialStore(underlyingAST, parameters);

        // Add receiver value
        if (underlyingAST instanceof UnderlyingAST.CFGMethod) {
            UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
            MethodTree methodDeclTree = method.getMethod();
            if (!TreeUtils.isConstructor(methodDeclTree) && methodDeclTree.getReceiverParameter() != null) {
                AnnotatedTypeMirror thisType = atypeFactory.getAnnotatedType(methodDeclTree.getReceiverParameter());
                initStore.initializeThisValue(thisType.getAnnotationInHierarchy(
                                AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), UnderInitialization.class)),
                        thisType.getUnderlyingType());
            }
        }

        return initStore;
    }

    @Override
    public TransferResult<CFValue, PackingStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<CFValue, PackingStore> in) {
        PackingStore store = in.getRegularStore();
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        if (receiver instanceof ClassNameNode) {
            String receiverName = ((ClassNameNode) receiver).getElement().toString();

            if (receiverName.equals(Packing.class.getName())) {
                JavaExpression objToPack = JavaExpression.fromNode(n.getArgument(0));

                ClassNameNode className = (ClassNameNode) ((FieldAccessNode) n.getArgument(1)).getReceiver();
                TypeMirror typeArg = ClassUtils.typeForName(
                        ((Symbol.ClassSymbol) className.getElement()).getQualifiedName().toString(),
                        (PackingFieldAccessSubchecker) atypeFactory.getChecker()
                );

                TypeMirror typeToPackTo;

                if (method.getSimpleName().contentEquals("pack")) {
                    typeToPackTo = typeArg;
                } else /*if (method.getSimpleName().contentEquals("unpack"))*/ {
                    typeToPackTo = TypesUtils.getSuperclass(typeArg, analysis.getTypes());
                }

                if (typeToPackTo == null) {
                    // This happens when the user tries to unpack from a type with no super type.
                    store.insertValue(objToPack, AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), FBCBottom.class));
                    return new RegularTransferResult<>(null, store, true);
                }

                CFValue oldVal = store.getValue(objToPack);
                AnnotationMirror newAnnotation;
                if (TypesUtils.getTypeElement(typeToPackTo).getModifiers().contains(Modifier.FINAL)) {
                    newAnnotation = AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), Initialized.class);
                } else if (oldVal != null && AnnotationUtils.containsSameByClass(oldVal.getAnnotations(), UnknownInitialization.class)) {
                    newAnnotation = atypeFactory.createUnknownInitializationAnnotation(typeToPackTo);
                } else {
                    newAnnotation = atypeFactory.createUnderInitializationAnnotation(typeToPackTo);
                }

                store.insertValue(objToPack, newAnnotation);
                return new RegularTransferResult<>(null, store, true);
            }
        }

        return super.visitMethodInvocation(n, in);
    }

    @Override
    protected void processPostconditions(Node invocationNode, PackingStore store, ExecutableElement executableElement, ExpressionTree invocationTree) {
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

            Node receiver = ((MethodInvocationNode) invocationNode).getTarget().getReceiver();
            AnnotatedTypeFactory.ParameterizedExecutableType method =
                    analysis.getTypeFactory().methodFromUse((MethodInvocationTree) invocationNode.getTree());

            if (executableElement.getKind().equals(ElementKind.CONSTRUCTOR)) {
                // For this() and super() calls, set receiver output type to constructor type
                AnnotatedTypeMirror receiverType = atypeFactory.getAnnotatedType(executableElement).getReturnType();
                if (receiverType != null) {
                    CFValue receiverDefaultValue = new CFValue(
                            analysis,
                            receiverType.getAnnotations(),
                            receiverType.getUnderlyingType());
                    store.replaceValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
                }
            } else {
                // For normal method calls, set receiver output type to input type by default.
                AnnotatedTypeMirror receiverType = method.executableType.getReceiverType();
                if (receiverType != null) {
                    CFValue receiverDefaultValue = new CFValue(
                            analysis,
                            receiverType.getAnnotations(),
                            receiverType.getUnderlyingType());
                    store.replaceValue(JavaExpression.fromNode(receiver), receiverDefaultValue);
                }
            }

            // Set parameter output types to input type by default.
            int i = 0;
            for (AnnotatedTypeMirror paramType : method.executableType.getParameterTypes()) {
                CFValue paramDefaultValue = new CFValue(
                        analysis,
                        paramType.getAnnotations(),
                        paramType.getUnderlyingType());
                store.replaceValue(
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
                CFValue paramDefaultValue = new CFValue(
                        analysis,
                        paramType.getAnnotations(),
                        paramType.getUnderlyingType());
                store.replaceValue(
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
