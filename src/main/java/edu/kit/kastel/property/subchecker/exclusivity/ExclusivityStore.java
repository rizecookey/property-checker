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
        var fieldPath = Stream.iterate(expression,
                        e -> e instanceof FieldAccess,
                        e -> ((FieldAccess) e).getReceiver())
                .toList()
                .reversed();

        // first component of field path. based on that, we derive the exclusivity type of the complete field access.
        JavaExpression root = fieldPath.isEmpty() ? expression : ((FieldAccess) fieldPath.getFirst()).getReceiver();
        var exclType = AnnotatedTypeMirror.createType(root.getType(), factory, false);
        exclType.addAnnotation(exclAnnotation(root));
        return factory.deriveExclusivityValue(exclType, expression);
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
