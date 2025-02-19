package edu.kit.kastel.property.subchecker.exclusivity;

import edu.kit.kastel.property.packing.PackingClientStore;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.dataflow.expression.MethodCall;
import org.checkerframework.framework.type.AnnotatedTypeMirror;

import javax.lang.model.element.AnnotationMirror;
import java.util.List;
import java.util.stream.Stream;

public class ExclusivityStore extends PackingClientStore<ExclusivityValue, ExclusivityStore> {

    private final ExclusivityViewpointAdapter viewpointAdapter;

    protected ExclusivityStore(ExclusivityAnalysis analysis, boolean sequentialSemantics) {
        super(analysis, sequentialSemantics);
        this.viewpointAdapter = ((ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory()).createViewpointAdapter();
    }

    protected ExclusivityStore(ExclusivityStore other) {
        super(other);
        this.viewpointAdapter = other.viewpointAdapter;
    }

    @Override
    protected boolean shouldInsert(JavaExpression expr, @Nullable ExclusivityValue value, boolean permitNondeterministic) {
        if (!canInsertJavaExpression(expr)) {
            return false;
        }

        ExclusivityAnnotatedTypeFactory factory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory();
        ExclusivityValue oldValue = getValue(expr);

        return super.shouldInsert(expr, value, permitNondeterministic) &&
                (oldValue == null || !factory.getQualifierHierarchy().isSubtypeQualifiersOnly(
                factory.getExclusivityAnnotation(getValue(expr).getAnnotations()),
                factory.EXCL_BOTTOM));
    }

    @Nullable
    public AnnotationMirror deriveExclusivityValue(JavaExpression expression) {
        var factory = ((ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory());
        // a.b, a.b.c, ..., expression (or empty if expression is not a field access)
        List<? extends JavaExpression> fieldPath = Stream.iterate(expression,
                        e -> e instanceof FieldAccess,
                        e -> ((FieldAccess) e).getReceiver())
                .toList()
                .reversed();

        if (fieldPath.isEmpty()) {
            // expression is not a field access
            return exclAnnotation(expression);
        }

        // first component of field path. based on that, we derive the exclusivity type of the complete field access.
        JavaExpression root = ((FieldAccess) fieldPath.getFirst()).getReceiver();
        var exclType = AnnotatedTypeMirror.createType(root.getType(), factory, false);
        var rootAnno = exclAnnotation(root);
        if (rootAnno == null) {
            return null;
        }
        exclType.addAnnotation(rootAnno);
        // fieldPath only contains FieldAccesses but can't be declared as List<FieldAccess> due to generics limitations
        //noinspection unchecked
        for (FieldAccess component : (List<FieldAccess>) fieldPath) {
            var field = component.getField();
            var declaredType = factory.getAnnotatedType(field);
            viewpointAdapter.viewpointAdaptMember(exclType, field, declaredType);
            exclType = declaredType;
        }

        return factory.getExclusivityAnnotation(exclType);
    }

    private AnnotationMirror exclAnnotation(JavaExpression expr) {
        var val = getValue(expr);
        var factory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory();
        if (val != null) {
            return factory.getExclusivityAnnotation(val.getAnnotations());
        } else if (expr instanceof MethodCall mc) {
            // for method calls, we default to the declared return exclusivity type
            var methodType = factory.getAnnotatedType(mc.getElement());
            // TODO: does this need to be viewpoint-adapted too?
            return factory.getExclusivityAnnotation(methodType.getReturnType());
        }
        return null;
    }
}
