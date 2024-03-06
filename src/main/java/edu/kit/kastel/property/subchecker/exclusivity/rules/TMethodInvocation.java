package edu.kit.kastel.property.subchecker.exclusivity.rules;

import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnalysis;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityValue;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

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
        TypeMirror receiverType = node.getTarget().getMethod().getReceiverType();
        AnnotationMirror receiverTypeAnno = null;
        boolean sideEffectFree = factory.isSideEffectFree(node.getTarget().getMethod());

        if (!ElementUtils.isStatic(TreeUtils.elementFromUse(node.getTree()))
                && !node.getTarget().getMethod().getSimpleName().contentEquals("<init>")) {
            if (receiverType == null || receiverType.getKind().equals(TypeKind.NONE)) {
                //TODO
                System.err.printf("warning: ignoring call to method without explicit 'this' parameter declaration: %s\n", node.getTarget());
                return;
            }

            // "param_0 = arg_0"
            //System.out.printf("%s(", node.getTarget().getMethod().getSimpleName());
            receiverTypeAnno = factory.getExclusivityAnnotation(factory.getAnnotatedType(node.getTarget().getMethod()).getReceiverType());
            if (sideEffectFree) {
                new TAssign(store, factory, analysis).applyWithoutInvalidation(receiverTypeAnno, receiver);
            } else {
                new TAssign(store, factory, analysis).applyOrInvalidate(receiverTypeAnno, receiver);
            }
        }

        // "param_i = arg_i;"
        for (int i = 0; i < node.getTarget().getMethod().getParameters().size(); ++i) {
            VariableElement paramDecl = node.getTarget().getMethod().getParameters().get(i);
            Node paramValue = node.getArgument(i);
            AnnotationMirror paramTypeAnno = factory.getExclusivityAnnotation(factory.getAnnotatedType(paramDecl));
            if (sideEffectFree) {
                new TAssign(store, factory, analysis).applyWithoutInvalidation(paramTypeAnno, paramValue);
            } else {
                new TAssign(store, factory, analysis).applyOrInvalidate(paramTypeAnno, paramValue);
            }
        }
        //System.out.print(")");

        // Rule is for x = mth(...), logic for refinement of x is in T-Method-Invocation-Helper
        /*TypeMirror returnType = node.getTarget().getMethod().getReturnType();
        if (!(returnType instanceof Type.JCVoidType)) {
            AnnotationMirror returnTypeAnno = factory.getExclusivityAnnotation(returnType.getAnnotationMirrors());
            System.out.printf(" -> %s\n", prettyPrint(returnTypeAnno));
        }*/

        // Remove possibly invalidated refinements
        if (store != null && analysis != null && !sideEffectFree) {
            boolean thisPassedAsArgument = receiverTypeAnno != null &&
                    receiver instanceof ThisNode &&
                    hierarchy.isSubtypeQualifiersOnly(receiverTypeAnno, factory.MAYBE_ALIASED);
            for (int i = 0; i < node.getArguments().size(); ++i) {
                Node arg = node.getArgument(i);
                AnnotationMirror argAnno = factory.getExclusivityAnnotation(node.getTarget().getMethod().getParameters().get(i).asType().getAnnotationMirrors());
                if (arg instanceof ThisNode && hierarchy.isSubtypeQualifiersOnly(argAnno, factory.MAYBE_ALIASED)) {
                    thisPassedAsArgument = true;
                    break;
                }
            }

            // Clear field values if they were possibly changed
            if (!sideEffectFree && thisPassedAsArgument) {
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

                CFValue receiverOutputPackingValue = packingFactory.getStoreAfter(node).getValue((ThisNode) null);
                AnnotatedTypeMirror receiverOutputPackingType = AnnotatedTypeMirror.createType(receiverType, packingFactory, false);
                if (receiverOutputPackingValue != null) {
                    receiverOutputPackingType.addAnnotations(receiverOutputPackingValue.getAnnotations());
                }

                AnnotatedTypeMirror receiverInputPackingType = packingFactory.getReceiverType(node.getTree());

                for (FieldAccess field : Set.copyOf(store.getFieldValues().keySet())) {
                    TypeMirror fieldOwnerType = field.getField().getEnclosingElement().asType();

                    // Don't clear invalidated values
                    if (hierarchy.isSubtypeQualifiersOnly(
                            factory.getExclusivityAnnotation(store.getValue(field).getAnnotations()),
                            factory.EXCL_BOTTOM)) {
                        continue;
                    }

                    // Don't clear fields in frame of UnknownInit input type
                    if (receiverInputPackingType.hasAnnotation(UnknownInitialization.class) &&
                            packingFactory.isInitializedForFrame(receiverInputPackingType, fieldOwnerType)) {
                        continue;
                    }

                    // For remaining fields in frame of output type, add declared type to store
                    if (receiverOutputPackingValue != null && packingFactory.isInitializedForFrame(receiverOutputPackingType, fieldOwnerType)) {
                        AnnotatedTypeMirror adaptedType = factory.getAnnotatedType(field.getField());
                        store.replaceValue(
                                field,
                                new ExclusivityValue(analysis,
                                        adaptedType.getAnnotations(),
                                        adaptedType.getUnderlyingType()));
                        //System.out.printf("Resetting refinement to declared type for %s after %s\n", field, node);
                        continue;
                    }

                    // For remaining params, clear value
                    store.clearValue(field);
                    //System.out.printf("Clearing refinement for %s after %s\n", field, node);
                }
            }
        }
    }


    @Override
    public String getName() {
        return "U-Method-Invocation";
    }
}
