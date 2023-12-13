package edu.kit.kastel.property.subchecker.exclusivity.rules;

import com.sun.tools.javac.code.Type;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import org.checkerframework.dataflow.cfg.node.ExplicitThisNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFStore;
import org.checkerframework.framework.flow.CFTransfer;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.util.Set;

public class TMethodInvocation extends AbstractTypeRule<MethodInvocationNode> {
    public TMethodInvocation(CFStore store, ExclusivityAnnotatedTypeFactory factory, CFAbstractAnalysis<CFValue, CFStore, CFTransfer> analysis) {
        super(store, factory, analysis);
    }

    @Override
    protected void applyInternal(MethodInvocationNode node) {
        Node receiver = node.getTarget().getReceiver();
        TypeMirror receiverType;
        receiverType = node.getTarget().getMethod().getReceiverType();

        if (receiverType == null || receiverType.getKind().equals(TypeKind.NONE)) {
            //TODO
            System.err.printf("warning: ignoring call to method without explicit 'this' parameter declaration: %s\n", node.getTarget());
            return;
        }

        System.out.printf("%s(", node.getTarget().getMethod().getSimpleName());
        AnnotationMirror receiverTypeAnno = factory.getExclusivityAnnotation(receiverType.getAnnotationMirrors());
        new TAssign(store, factory, analysis).applyOrInvalidate(receiverTypeAnno, receiver);

        // "param_i = arg_i;"
        int i = 0;
        for (VariableElement paramDecl : node.getTarget().getMethod().getParameters()) {
            Node paramValue = node.getArgument(i++);
            AnnotationMirror paramTypeAnno = factory.getExclusivityAnnotation(paramDecl.asType().getAnnotationMirrors());
            new TAssign(store, factory, analysis).applyOrInvalidate(paramTypeAnno, paramValue);
        }
        System.out.print(")");

        // Rule is for x = mth(...), logic for refinement of x is in T-Method-Invocation-Helper
        TypeMirror returnType = node.getTarget().getMethod().getReturnType();
        if (!(returnType instanceof Type.JCVoidType)) {
            AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(returnType.getAnnotationMirrors());
            System.out.printf(" -> %s\n", prettyPrint(returnTypeAnno));
        }

        // Remove possibly invalidated refinements
        if (store != null && analysis != null) {
            CFValue thisValue = store.getValue((ThisNode) null);
            AnnotationMirror thisType;
            if (thisValue != null) {
                thisType = factory.getExclusivityAnnotation(thisValue.getAnnotations());
            } else {
                AnnotatedTypeMirror.AnnotatedDeclaredType currentMethodReceiverType =
                        factory.getAnnotatedType(factory.getContainingMethod(node))
                                .getReceiverType();

                if (currentMethodReceiverType == null) {
                    System.err.printf("warning: ignoring call in method without explicit 'this' parameter declaration: %s\n",
                            analysis.getContainingMethod(node.getTree()));
                    return;
                }

                thisType = factory.getExclusivityAnnotation(
                        currentMethodReceiverType.getAnnotations());
            }

            if (receiver instanceof ThisNode || !factory.mayHoldProperty(thisType)) {
                // Copy keySet to prevent ConcurrentModificationException due to clearValue
                for (FieldAccess field : Set.copyOf(store.getFieldValues().keySet())) {
                    if (!hierarchy.isSubtypeQualifiersOnly(
                            factory.getExclusivityAnnotation(store.getValue(field).getAnnotations()),
                            factory.EXCLUSIVITY_BOTTOM)) {
                        store.clearValue(field);
                        System.out.printf("Clearing refinement for %s after %s\n",
                                field, node);
                    }
                }
            }
        }
    }

    @Override
    public String getName() {
        return "T-Method-Invocation";
    }
}
