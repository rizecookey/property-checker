package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.*;

import java.util.Set;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.common.basetype.TypeValidator;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedDeclaredType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedPrimitiveType;

public class ExclusivityVisitor extends BaseTypeVisitor<ExclusivityAnnotatedTypeFactory> {
    public ExclusivityVisitor(BaseTypeChecker checker) {
        super(checker);
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
        try {
            MemberSelectTree lhs = (MemberSelectTree) node.getVariable();
            try {
                IdentifierTree ident = (IdentifierTree) lhs.getExpression();
                if (ident.getName().contentEquals("this")) {
                    if (!atypeFactory.isMutable(atypeFactory.getAnnotatedType(ident))) {
                        // T-Assign: lhs is local var OR this is modifiable
                        checker.reportError(node, "assignment.this-not-writable");
                    }
                } else {
                    // Field access is only allowed to fields of this, not other objects
                    checker.reportError(node, "assignment.invalid-lhs");
                }
            } catch (ClassCastException e) {
                // No field access to arbitrary expressions is allowed
                checker.reportError(node, "assignment.invalid-lhs");
            }
        } catch (ClassCastException ignored) {}

        // TODO Not thread-safe :-)
        atypeFactory.useIFlowAfter(node);
        validateTypeOf(node.getExpression());
        validateTypeOf(node.getVariable());
        atypeFactory.useRegularIFlow();

        //return super.visitAssignment(node, p);
        return p;
    }

    @Override
    public Void visitMethodInvocation(MethodInvocationTree node, Void p) {
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
    
    @Override
    public boolean isValidUse(AnnotatedPrimitiveType type, Tree tree) {
        return super.isValidUse(type, tree)
                // Primitives are always immutable and must never
                // be annotated as mutable
                && atypeFactory.getQualifierHierarchy().isSubtype(
                        atypeFactory.IMMUTABLE,
                        type.getAnnotationInHierarchy(atypeFactory.READ_ONLY));
    }
    
    @SuppressWarnings("nls")
    @Override
    public boolean isValidUse(AnnotatedDeclaredType declarationType,
            AnnotatedDeclaredType useType, Tree tree) {
        if (declarationType.getUnderlyingType().asElement().toString().equals("java.lang.String")) {
            return super.isValidUse(declarationType, useType, tree)
                    // Strings are always immutable and must never
                    // be annotated as mutable
                    && atypeFactory.getQualifierHierarchy().isSubtype(
                    atypeFactory.IMMUTABLE,
                    useType.getAnnotationInHierarchy(atypeFactory.READ_ONLY));
        } else {
            return super.isValidUse(declarationType, useType, tree);
        }
    }

    @Override
    protected TypeValidator createTypeValidator() {
        return new ExclusivityValidator(checker, this, atypeFactory);
    }
    
    @SuppressWarnings("nls")
    @Override
    protected void checkConstructorResult(
            AnnotatedExecutableType constructorType, ExecutableElement constructorElement) {
        // A constructor result can be refined to any type (see TRefNew),
        // so we return a warning if the user unnecessarily overwrites the default.
        QualifierHierarchy qualifierHierarchy = atypeFactory.getQualifierHierarchy();
        Set<AnnotationMirror> constructorAnnotations =
                constructorType.getReturnType().getAnnotations();
        
        AnnotationMirror constructorAnno =
                qualifierHierarchy.findAnnotationInHierarchy(constructorAnnotations, atypeFactory.EXCL_MUT);
        if (!qualifierHierarchy.isSubtype(atypeFactory.EXCL_MUT, constructorAnno)) {
            checker.reportWarning(
                    constructorElement, "unnecessary.constructor.type", constructorAnno, atypeFactory.EXCL_MUT);
        }
    }
    
    @Override
    protected void commonAssignmentCheck(
            AnnotatedTypeMirror varType,
            AnnotatedTypeMirror valueType,
            Tree valueTree,
            @CompilerMessageKey String errorKey,
            Object... extraArgs) {
        if (valueTree instanceof NewClassTree) {
            // A constructor result can be of any type, as this cannot be leaked
            // in the constructor except as ReadOnly,
            // so ignore any error here.
            return;
        }
        
        super.commonAssignmentCheck(varType, valueType, valueTree, errorKey, extraArgs);
    }
}
