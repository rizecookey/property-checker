package edu.kit.kastel.property.packing;

import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.initialization.InitializationAbstractTransfer;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import java.lang.reflect.Modifier;

public class PackingTransfer extends InitializationAbstractTransfer<CFValue, PackingStore, PackingTransfer> {

    public PackingTransfer(PackingAnalysis analysis) {
        super(analysis);
    }

    @Override
    public TransferResult<CFValue, PackingStore> visitMethodInvocation(
            MethodInvocationNode n, TransferInput<CFValue, PackingStore> in) {
        MethodAccessNode target = n.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        if (receiver instanceof ClassNameNode) {
            String receiverName = ((ClassNameNode) receiver).getElement().toString();

            if (receiverName.equals(Packing.class.getName())) {
                PackingStore store = in.getRegularStore();

                JavaExpression objToPack = JavaExpression.fromNode(n.getArgument(0));

                Class<?> clazzArg = ClassUtils.classOrPrimitiveForName(
                        ((FieldAccessNode) n.getArgument(1)).getReceiver().toString(),
                        (PackingFieldAccessSubchecker) atypeFactory.getChecker()
                );

                Class<?> clazzToPackTo;

                if (method.getSimpleName().contentEquals("pack")) {
                    clazzToPackTo = clazzArg;
                } else /*if (method.getSimpleName().contentEquals("unpack"))*/ {
                    clazzToPackTo = clazzArg.getSuperclass();
                }

                CFValue oldVal = store.getValue(objToPack);
                AnnotationMirror newAnnotation;
                if (Modifier.isFinal(clazzToPackTo.getModifiers())) {
                    newAnnotation = AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), Initialized.class);
                } else if (oldVal != null && AnnotationUtils.containsSameByClass(oldVal.getAnnotations(), UnknownInitialization.class)) {
                    newAnnotation = atypeFactory.createUnknownInitializationAnnotation(clazzToPackTo);
                } else {
                    newAnnotation = atypeFactory.createUnderInitializationAnnotation(clazzToPackTo);
                }

                store.insertValue(objToPack, newAnnotation);

                return new RegularTransferResult<>(null, store, true);
            }
        }

        return super.visitMethodInvocation(n, in);
    }
}
