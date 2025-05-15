package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.framework.type.AbstractViewpointAdapter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;

public class ExclusivityViewpointAdapter extends AbstractViewpointAdapter {

    protected ExclusivityAnnotatedTypeFactory atypeFactory;

    public ExclusivityViewpointAdapter(ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(atypeFactory);
        this.atypeFactory = atypeFactory;
    }

    @Override
    protected AnnotationMirror extractAnnotationMirror(AnnotatedTypeMirror atm) {
        return atypeFactory.getExclusivityAnnotation(atm);
    }

    @Override
    protected AnnotationMirror combineAnnotationWithAnnotation(
            AnnotationMirror receiverAnnotation, AnnotationMirror declaredAnnotation
    ) {
        if (AnnotationUtils.areSame(declaredAnnotation, atypeFactory.UNIQUE)) {
            return receiverAnnotation;
        } else {
            return declaredAnnotation;
        }
    }

    @Override
    protected AnnotatedTypeMirror combineAnnotationWithType(
            AnnotationMirror receiverAnnotation, AnnotatedTypeMirror declaredType) {
        AnnotatedTypeMirror result = AnnotatedTypeMirror.createType(
                declaredType.getUnderlyingType(), atypeFactory, declaredType.isDeclaration());
        if (declaredType.getPrimitiveKind() != null) {
            result.addAnnotation(atypeFactory.UNIQUE);
            return result;
        } else if (declaredType.hasAnnotation(atypeFactory.UNIQUE)) {
            result.addAnnotation(receiverAnnotation);
            return result;
        } else {
            result.addAnnotation(declaredType.getAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        }
    }

    @Override
    protected AnnotatedTypeMirror combineTypeWithType(
            AnnotatedTypeMirror receiverType, AnnotatedTypeMirror declaredType) {
        AnnotatedTypeMirror result = AnnotatedTypeMirror.createType(
                declaredType.getUnderlyingType(), atypeFactory, declaredType.isDeclaration());
        if (TypesUtils.isPrimitive(declaredType.getUnderlyingType())) {
            result.addAnnotation(atypeFactory.UNIQUE);
            return result;
        } else if (declaredType.hasAnnotation(atypeFactory.UNIQUE)) {
            result.addAnnotation(receiverType.getEffectiveAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        } else {
            result.addAnnotation(declaredType.getEffectiveAnnotationInHierarchy(atypeFactory.UNIQUE));
            return result;
        }
    }

    @Override
    public void viewpointAdaptMethod(AnnotatedTypeMirror receiverType, ExecutableElement methodElt, AnnotatedTypeMirror.AnnotatedExecutableType methodType) {
        // do nothing
    }

    @Override
    public void viewpointAdaptConstructor(AnnotatedTypeMirror receiverType, ExecutableElement constructorElt, AnnotatedTypeMirror.AnnotatedExecutableType constructorType) {
        // do nothing
    }
}
