package edu.kit.kastel.property.packing;

import com.sun.source.tree.MethodTree;
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
import org.checkerframework.dataflow.expression.ClassName;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import java.lang.reflect.Modifier;
import java.util.List;

public class PackingTransfer extends InitializationAbstractTransfer<CFValue, PackingStore, PackingTransfer> {

    public PackingTransfer(PackingAnalysis analysis) {
        super(analysis);
    }

    @Override
    public PackingStore initialStore(UnderlyingAST underlyingAST, List<LocalVariableNode> parameters) {
        UnderlyingAST.CFGMethod method = (UnderlyingAST.CFGMethod) underlyingAST;
        MethodTree methodDeclTree = method.getMethod();
        ExecutableElement methodElem = TreeUtils.elementFromDeclaration(methodDeclTree);

        PackingStore initStore = super.initialStore(underlyingAST, parameters);
        if (methodDeclTree.getReceiverParameter() != null) {
            AnnotatedTypeMirror thisType = atypeFactory.getAnnotatedType(methodDeclTree.getReceiverParameter());
            initStore.initializeThisValue(thisType.getAnnotationInHierarchy(
                    AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), UnderInitialization.class)),
                    thisType.getUnderlyingType());
        }
        return initStore;
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

                ClassNameNode className = (ClassNameNode) ((FieldAccessNode) n.getArgument(1)).getReceiver();
                Class<?> clazzArg = ClassUtils.classOrPrimitiveForName(
                        ((Symbol.ClassSymbol) className.getElement()).getQualifiedName().toString(),
                        (PackingFieldAccessSubchecker) atypeFactory.getChecker()
                );

                Class<?> clazzToPackTo;

                if (method.getSimpleName().contentEquals("pack")) {
                    clazzToPackTo = clazzArg;
                } else /*if (method.getSimpleName().contentEquals("unpack"))*/ {
                    clazzToPackTo = clazzArg.getSuperclass();
                }

                if (clazzToPackTo == null) {
                    // This happens when the user tries to unpack from a type with no super type.
                    store.insertValue(objToPack, AnnotationBuilder.fromClass(atypeFactory.getElementUtils(), FBCBottom.class));
                    return new RegularTransferResult<>(null, store, true);
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
