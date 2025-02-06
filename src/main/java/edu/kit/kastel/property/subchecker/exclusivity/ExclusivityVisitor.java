package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;
import com.sun.tools.javac.code.Type;
import edu.kit.kastel.property.packing.PackingClientVisitor;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.javacutil.AnnotationMirrorSet;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.annotation.processing.ProcessingEnvironment;
import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

public final class ExclusivityVisitor extends PackingClientVisitor<ExclusivityAnnotatedTypeFactory> {

    private final ExecutableElement packMethod;
    private final ExecutableElement unpackMethod;

    public ExclusivityVisitor(BaseTypeChecker checker) {
        super(checker);
       packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, atypeFactory.getProcessingEnv());
        unpackMethod = TreeUtils.getMethod(Packing.class, "unpack", 2, atypeFactory.getProcessingEnv());
    }

    @Override
    public Void visitAnnotation(AnnotationTree tree, Void p) {
        // do nothing
        return null;
    }

    @Override
    public Void visitVariable(VariableTree node, Void p) {
        // TODO Not thread-safe :-)
        atypeFactory.useIFlowAfter(node);
        validateType(node, atypeFactory.getAnnotatedTypeLhs(node));
        if (node.getInitializer() != null) {
            validateTypeOf(node.getInitializer());
        }
        atypeFactory.useRegularIFlow();
        //return super.visitAssignment(node, p);
        return p;
    }

    @Override
    public Void visitAssignment(AssignmentTree node, Void p) {
        // TODO Not thread-safe :-)
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node.getExpression());
        validateTypeOf(node.getVariable());
        atypeFactory.useRegularIFlow();

        ExpressionTree lhs = node.getVariable();

        if (lhs instanceof MemberSelectTree) {
            // Field access
            MemberSelectTree lhsField = (MemberSelectTree) lhs;
            try {
                IdentifierTree ident = (IdentifierTree) lhsField.getExpression();
                // Field access is only allowed to fields of this, not other objects
                if (!ident.getName().contentEquals("this")) {
                    checker.reportError(node, "assignment.invalid-lhs");
                }
                // Field access is only allowed if this is not ReadOnly
                if (atypeFactory.getAnnotatedType(ident).hasAnnotation(atypeFactory.READ_ONLY)) {
                    // T-Assign: lhs is local var OR this is modifiable
                    checker.reportError(node, "assignment.this-not-writable");
                }
            } catch (ClassCastException e) {
                // No field access to arbitrary expressions is allowed
                checker.reportError(node, "assignment.invalid-lhs");
            }
            return p;
        } else if (isParam(lhs)) {
            // Parameters must not be reassigned
            checker.reportError(node, "assignment.parameter");
            return p;
        } else {
            // Local variable. Everything is checked by the transfer rules; nothing to do here.
            return p;
        }
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
        ExecutableElement invokedMethod = TreeUtils.elementFromUse(node);
        ProcessingEnvironment env = atypeFactory.getProcessingEnv();

        if (ElementUtils.isMethod(invokedMethod, packMethod, env) || ElementUtils.isMethod(invokedMethod, unpackMethod, env)) {
            ExpressionTree objToPack = node.getArguments().get(0);
            if (!qualHierarchy.isSubtypeQualifiersOnly(
                    atypeFactory.getExclusivityAnnotation(atypeFactory.getAnnotatedType(objToPack)),
                    atypeFactory.UNIQUE)) {
                checker.reportError(node, "exclusivity.packing.aliased");
            }
            return null;
        }

        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node);
        ExpressionTree recv = node.getMethodSelect();
        validateTypeOf(recv);
        if (recv instanceof MemberSelectTree) {
            validateTypeOf(((MemberSelectTree) recv).getExpression());
        }
        for (ExpressionTree arg : node.getArguments()) {
            validateTypeOf(arg);
        }
        atypeFactory.useRegularIFlow();
        return p;
    }

    @Override
    public Void visitReturn(ReturnTree node, Void p) {
        // Don't try to check return expressions for void methods.
        if (node.getExpression() == null) {
            return super.visitReturn(node, p);
        }
        
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node.getExpression());
        atypeFactory.useRegularIFlow();
        return p;
    }
    
   /* @Override
    public boolean isValidUse(AnnotatedPrimitiveType type, Tree tree) {
        return super.isValidUse(type, tree)
                && type.hasAnnotation(atypeFactory.UNIQUE);
    }
    
    @SuppressWarnings("nls")
    @Override
    public boolean isValidUse(AnnotatedDeclaredType declarationType,
            AnnotatedDeclaredType useType, Tree tree) {
        if (declarationType.getUnderlyingType().asElement().toString().equals("java.lang.String")) {
            return super.isValidUse(declarationType, useType, tree)
                    && useType.hasAnnotation(atypeFactory.MAYBE_ALIASED);
        } else {
            return super.isValidUse(declarationType, useType, tree);
        }
    }*/

    @Override
    protected TypeValidator createTypeValidator() {
        return new ExclusivityValidator(checker, this, atypeFactory);
    }

    @Override
    protected AnnotationMirror defaultConstructorQualifier(Type classType) {
        return atypeFactory.UNIQUE;
    }

    @Override
    protected void checkImplicitConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // For implicit default constructors, the default type @Unique is always correct and exact, so there's
        // nothing to do here.
    }

    @Override
    protected String getContractPostconditionNotSatisfiedMessage() {
        return "exclusivity.postcondition.not.satisfied";
    }

    @Override
    protected AnnotationMirrorSet getExceptionParameterLowerBoundAnnotations() {
        return AnnotationMirrorSet.singleton(atypeFactory.MAYBE_ALIASED);
    }

    @Override
    protected boolean commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        if (valueTree instanceof NewClassTree) {
            // A constructor result can be of any type, as this cannot be leaked
            // in the constructor except as ReadOnly,
            // so ignore any error here.
            return true;
        }
        
        return super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
    }
}
