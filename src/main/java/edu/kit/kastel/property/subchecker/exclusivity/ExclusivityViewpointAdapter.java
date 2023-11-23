package edu.kit.kastel.property.subchecker.exclusivity;

import org.checkerframework.framework.type.AbstractViewpointAdapter;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.QualifierHierarchy;

import javax.lang.model.element.AnnotationMirror;

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
        QualifierHierarchy hierarchy = atypeFactory.getQualifierHierarchy();
        if (hierarchy.isSubtype(declaredAnnotation, atypeFactory.EXCL_MUT)
                && !hierarchy.isSubtype(receiverAnnotation, atypeFactory.EXCL_MUT)) {
            return atypeFactory.RESTRICTED;
        } else if (hierarchy.isSubtype(declaredAnnotation, atypeFactory.SHR_MUT)
                && !atypeFactory.isMutable(receiverAnnotation)) {
            return atypeFactory.READ_ONLY;
        } else {
            return declaredAnnotation;
        }
    }
}
