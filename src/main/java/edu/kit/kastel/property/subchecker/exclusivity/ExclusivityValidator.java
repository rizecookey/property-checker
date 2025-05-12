package edu.kit.kastel.property.subchecker.exclusivity;

import com.sun.source.tree.ParameterizedTypeTree;
import com.sun.source.tree.Tree;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeValidator;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.DiagMessage;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.tools.Diagnostic;
import java.util.Collections;
import java.util.List;

public class ExclusivityValidator extends BaseTypeValidator
{
    protected ExclusivityAnnotatedTypeFactory atypeFactory;

    public ExclusivityValidator(BaseTypeChecker checker, BaseTypeVisitor<?> visitor, ExclusivityAnnotatedTypeFactory atypeFactory) {
        super(checker, visitor, atypeFactory);
        this.atypeFactory = atypeFactory;
    }

    @Override
    protected Void visitParameterizedType(AnnotatedTypeMirror.AnnotatedDeclaredType type, ParameterizedTypeTree tree) {
        // nothing to check
        return null;
    }

    @Override
    protected List<DiagMessage> isValidStructurally(AnnotatedTypeMirror type) {
        AnnotationMirror typeAnno = atypeFactory.getExclusivityAnnotation(type.getAnnotations());
        if (typeAnno == null) {
            return Collections.emptyList();
        }

        List<DiagMessage> msgList = !AnnotationUtils.areSame(typeAnno, atypeFactory.EXCL_BOTTOM)
                ? Collections.emptyList()
                : Collections.singletonList(new DiagMessage(Diagnostic.Kind.ERROR, "exclusivity.type.invalidated"));

        return DiagMessage.mergeLists(msgList, super.isValidStructurally(type));
    }

    @Override
    protected boolean shouldCheckTopLevelDeclaredOrPrimitiveType(AnnotatedTypeMirror type, Tree tree) {
        return true;
    }
}
