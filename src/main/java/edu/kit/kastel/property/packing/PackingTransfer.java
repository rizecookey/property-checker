package edu.kit.kastel.property.packing;

import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.initialization.InitializationAbstractTransfer;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.javacutil.ElementUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

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

                JavaExpression obj = JavaExpression.fromNode(n.getArgument(0));

                Class<?> clazz = ClassUtils.classOrPrimitiveForName(
                        ((FieldAccessNode) n.getArgument(1)).getReceiver().toString(),
                        (PackingFieldAccessSubchecker) atypeFactory.getChecker()
                );

                if (method.getSimpleName().contentEquals("pack")) {
                    AnnotationMirror newAnnotation = atypeFactory.createUnderInitializationAnnotation(clazz);
                    store.insertValue(obj, newAnnotation);
                } else /*if (method.getSimpleName().contentEquals("unpack"))*/ {
                    AnnotationMirror newAnnotation = atypeFactory.createUnderInitializationAnnotation(clazz.getSuperclass());
                    store.insertValue(obj, newAnnotation);
                }

                return new RegularTransferResult<>(null, store);
            }
        }

        return super.visitMethodInvocation(n, in);
    }
}
