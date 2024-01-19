package edu.kit.kastel.property.packing;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.tree.JCTree;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.initialization.InitializationAbstractVisitor;
import org.checkerframework.checker.initialization.InitializationChecker;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.node.FieldAccessNode;
import org.checkerframework.framework.flow.CFAbstractStore;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.javacutil.*;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.*;
import javax.lang.model.type.TypeMirror;
import javax.lang.model.util.Types;
import java.util.List;
import java.util.StringJoiner;
import java.util.stream.Collectors;

public class PackingVisitor
        extends InitializationAbstractVisitor<CFValue, PackingStore, PackingTransfer, PackingAnalysis, PackingAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    public PackingVisitor(BaseTypeChecker checker) {
        super(checker);
        packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
    }

    @Override
    protected PackingAnnotatedTypeFactory createTypeFactory() {
        // Don't load the factory reflexively based on checker class name.
        // Instead, always use the PackingAnnotatedTypeFactory.
        return new PackingAnnotatedTypeFactory(checker);
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(node);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();

        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            ExpressionTree objToPack = node.getArguments().get(0);

            if (!objToPack.toString().equals("this")) {
                checker.reportError(node, "initialization.packing.nonreceiver");
            }

            Element typeElement = TreeUtils.elementFromUse(((MemberSelectTree) node.getArguments().get(1)).getExpression());
            TypeMirror newTypeFrame = types.getDeclaredType((TypeElement) typeElement);

            AnnotationMirror oldAnnotation = atypeFactory.getAnnotatedType(objToPack).getAnnotationInHierarchy(atypeFactory.getInitialized());
            TypeMirror oldTypeFrame;
            if (AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getUnknownInitialization())
                    || AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getUnderInitialization())) {
                oldTypeFrame = atypeFactory.getTypeFrameFromAnnotation(oldAnnotation);
            } else /*if (AnnotationUtils.areSameByName(oldAnnotation, atypeFactory.getInitialized()))*/ {
                Type enclosingClassType = ((JCTree) TreePathUtil.enclosingClass(getCurrentPath())).type;
                if (enclosingClassType.isFinal()) {
                    oldTypeFrame = enclosingClassType;
                } else {
                    oldTypeFrame = null;
                }
            }

            if (ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
                // Type-check unpack statement: new type frame must be supertype of old type frame.
                if (oldTypeFrame != null && (!types.isSubtype(oldTypeFrame, newTypeFrame) || types.isSameType(oldTypeFrame, newTypeFrame))) {
                    checker.reportError(node, "initialization.already.unpacked");
                }
            } else {
                // Type-check pack statement:
                // New type frame must be subtype of old type frame.
                if (oldTypeFrame == null || (!types.isSubtype(newTypeFrame, oldTypeFrame) || types.isSameType(oldTypeFrame, newTypeFrame))) {
                    checker.reportError(node, "initialization.already.packed");
                }

                //All fields in new frame must be initialized.
                checkFieldsInitializedUpToFrame(node, newTypeFrame);
            }

            return null;
        } else {
            return super.visitMethodInvocation(node, p);
        }
    }

    /**
     * Checks that all fields up to a given frame are initialized at a given pack statement.
     *
     * @param tree a pack statement
     * @param frame the type frame up to which the fields should be initialized
     */
    protected void checkFieldsInitializedUpToFrame(
            Tree tree,
            TypeMirror frame) {
        // Compact canonical record constructors do not generate visible assignments in the source,
        // but by definition they assign to all the record's fields so we don't need to
        // check for uninitialized fields in them:
        if (tree.getKind() == Tree.Kind.METHOD
                && TreeUtils.isCompactCanonicalRecordConstructor((MethodTree) tree)) {
            return;
        }

        GenericAnnotatedTypeFactory<?, ?, ?, ?> targetFactory =
                checker.getTypeFactoryOfSubcheckerOrNull(
                        ((InitializationChecker) checker).getTargetCheckerClass());
        List<VariableElement> uninitializedFields =
                atypeFactory.getUninitializedFields(
                        atypeFactory.getStoreBefore(tree),
                        targetFactory.getStoreBefore(tree),
                        getCurrentPath(),
                        false,
                        List.of()).stream()
                        .map(TreeUtils::elementFromDeclaration).collect(Collectors.toList());

        // Remove fields below frame
        uninitializedFields.retainAll(ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), elements));

        // Remove fields with a relevant @SuppressWarnings annotation
        uninitializedFields.removeIf(
                f -> checker.shouldSuppressWarnings(f, "initialization.field.uninitialized"));

        if (!uninitializedFields.isEmpty()) {
            StringJoiner fieldsString = new StringJoiner(", ");
            for (VariableElement f : uninitializedFields) {
                fieldsString.add(f.getSimpleName());
            }
            checker.reportError(tree, "initialization.fields.uninitialized", fieldsString);
        }
    }

    @Override
    protected void checkFieldsInitialized(
            Tree tree, boolean staticFields, PackingStore initExitStore, List<? extends AnnotationMirror> receiverAnnotations) {
        // TODO: For now, the packing checker only changes a reference's type for explicit (un-)pack statements.
        // When implementing implicit (un-)packing, change this override.

        // Still call the super class for static initializers and default constructors to avoid false negatives.
        if (staticFields || TreeUtils.isSynthetic((MethodTree) tree)) {
            super.checkFieldsInitialized(tree, staticFields, initExitStore, receiverAnnotations);
        }
    }
}
