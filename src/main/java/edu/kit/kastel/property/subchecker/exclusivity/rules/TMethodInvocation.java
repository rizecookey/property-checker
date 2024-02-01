package edu.kit.kastel.property.subchecker.exclusivity.rules;

import com.sun.source.tree.MethodTree;
import com.sun.tools.javac.code.Type;

import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.dataflow.cfg.node.ExplicitThisNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;
import java.util.Set;

public class TMethodInvocation extends AbstractTypeRule<MethodInvocationNode> {
    public TMethodInvocation(ExclusivityStore store, ExclusivityAnnotatedTypeFactory factory, ExclusivityAnalysis analysis) {
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

        // "param_0 = arg_0"
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
            // Clear field values if they were possibly changed
            if (!factory.isSideEffectFree(node.getTarget().getMethod())
                    && (receiver instanceof ThisNode && hierarchy.isSubtypeQualifiersOnly(receiverTypeAnno, factory.MAYBE_ALIASED))) {
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                CFValue receiverOutputPackingValue = packingFactory.getStoreAfter(node).getValue((ThisNode) null);
                AnnotatedTypeMirror receiverOutputPackingType = AnnotatedTypeMirror.createType(receiverType, packingFactory, false);
                if (receiverOutputPackingValue != null) {
                    receiverOutputPackingType.addAnnotations(receiverOutputPackingValue.getAnnotations());
                }

                for (FieldAccess field : Set.copyOf(store.getFieldValues().keySet())) {
                    TypeMirror fieldOwnerType = field.getField().getEnclosingElement().asType();

                    if (!hierarchy.isSubtypeQualifiersOnly(
                            factory.getExclusivityAnnotation(store.getValue(field).getAnnotations()),
                            factory.EXCL_BOTTOM)
                            && (receiverOutputPackingValue == null || !packingFactory.isInitializedForFrame(receiverOutputPackingType, fieldOwnerType))) {
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
        return "U-Method-Invocation";
    }
}
