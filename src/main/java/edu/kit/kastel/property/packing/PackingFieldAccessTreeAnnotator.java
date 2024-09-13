package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import org.checkerframework.checker.initialization.InitializationFieldAccessTreeAnnotator;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.Element;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;

public class PackingFieldAccessTreeAnnotator extends InitializationFieldAccessTreeAnnotator {

    private boolean uncommitPrimitiveFields;

    public PackingFieldAccessTreeAnnotator(GenericAnnotatedTypeFactory<?, ?, ?, ?> atypeFactory) {
        this(atypeFactory, true);
    }

    public PackingFieldAccessTreeAnnotator(GenericAnnotatedTypeFactory<?, ?, ?, ?> atypeFactory, boolean uncommitPrimitiveFields) {
        super(atypeFactory);
        this.uncommitPrimitiveFields = uncommitPrimitiveFields;
    }

    @Override
    public Void visitIdentifier(IdentifierTree tree, AnnotatedTypeMirror p) {
        super.visitIdentifier(tree, p);
        computeFieldAccessType(tree, p);
        return null;
    }

    @Override
    public Void visitMemberSelect(MemberSelectTree tree, AnnotatedTypeMirror p) {
        super.visitMemberSelect(tree, p);
        computeFieldAccessType(tree, p);
        return null;
    }

    /**
     * Adapts the type in the target checker hierarchy of a field access depending on the field's
     * declared type and the receiver's initialization type.
     *
     * @param tree the field access
     * @param type the field access's unadapted type
     */
    private void computeFieldAccessType(ExpressionTree tree, AnnotatedTypeMirror type) {
        GenericAnnotatedTypeFactory<?, ?, ?, ?> factory =
                (GenericAnnotatedTypeFactory<?, ?, ?, ?>) atypeFactory;

        if (!uncommitPrimitiveFields && type.getPrimitiveKind() != null) {
            return;
        }

        // Don't adapt anything if initialization checking is turned off.
        if (assumeInitialized || ((PackingFieldAccessAnnotatedTypeFactory) fieldAccessFactory).isComputingUninitializedFields()) {
            return;
        }

        if (fieldAccessFactory.getStoreBefore(tree) == null) {
            type.clearAnnotations();
            type.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
            return;
        }

        // Don't adapt anything if "tree" is not actually a field access.

        // Don't adapt uses of the identifiers "this" or "super" that are not field accesses
        // (e.g., constructor calls or uses of an outer this).
        if (tree instanceof IdentifierTree) {
            IdentifierTree identTree = (IdentifierTree) tree;
            if (identTree.getName().contentEquals("this")
                    || identTree.getName().contentEquals("super")) {
                return;
            }
        }

        // Don't adapt method accesses.
        if (type instanceof AnnotatedTypeMirror.AnnotatedExecutableType) {
            return;
        }

        // Don't adapt trees that do not have a (explicit or implicit) receiver (e.g., local
        // variables).
        CFValue receiverValue = ((PackingFieldAccessAnnotatedTypeFactory) fieldAccessFactory).getStoreBefore(tree).getValue((ThisNode) null);
        AnnotatedTypeMirror receiver;
        if (receiverValue != null) {
            receiver = AnnotatedTypeMirror.createType(receiverValue.getUnderlyingType(), fieldAccessFactory, false);
            receiver.addAnnotations(receiverValue.getAnnotations());
        } else {
            receiver = fieldAccessFactory.getReceiverType(tree);
        }
        if (receiver == null) {
            return;
        }

        // Don't adapt trees whose receiver is initialized.
        if (!fieldAccessFactory.isUnknownInitialization(receiver)
                && !fieldAccessFactory.isUnderInitialization(receiver)) {
            return;
        }

        Element element = TreeUtils.elementFromUse(tree);
        TypeMirror fieldOwnerType = element.getEnclosingElement().asType();

        if (fieldOwnerType.getKind() != TypeKind.DECLARED) {
            return;
        }

        boolean isReceiverInitToOwner =
                fieldAccessFactory.isInitializedForFrame(receiver, fieldOwnerType);

        // If the field declaration is null (because the field is declared in bytecode),
        // the field is considered committed.
        // Fields of objects other than this are not tracked and thus also considered committed.
        // Otherwise, check if the field is initialized in the given store.
        Tree fieldDeclarationTree = fieldAccessFactory.declarationFromElement(element);
        if (!isReceiverInitToOwner
                && fieldDeclarationTree != null
                && TreeUtils.isSelfAccess(tree)) {
            type.clearAnnotations();
            type.addAnnotations(factory.getQualifierHierarchy().getTopAnnotations());
        }
    }
}
