package edu.kit.kastel.property.packing;

import com.sun.source.util.TreePath;
import org.checkerframework.checker.initialization.InitializationFieldAccessAbstractAnnotatedTypeFactory;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.VariableElement;
import java.util.Collection;
import java.util.List;

public class PackingFieldAccessAnnotatedTypeFactory
        extends InitializationFieldAccessAbstractAnnotatedTypeFactory<CFValue, PackingStore, PackingTransfer, PackingAnalysis> {

    private boolean computingUninitializedFields = false;

    public PackingFieldAccessAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @Override
    protected PackingAnalysis createFlowAnalysis() {
        return new PackingAnalysis(checker, this);
    }

    @Override
    public PackingTransfer createFlowTransferFunction(
            CFAbstractAnalysis<CFValue, PackingStore, PackingTransfer> analysis) {
        return new PackingTransfer((PackingAnalysis) analysis);
    }

    public boolean isComputingUninitializedFields() {
        return computingUninitializedFields;
    }

    public void setComputingUninitializedFields(boolean computingUninitializedFields) {
        this.computingUninitializedFields = computingUninitializedFields;
    }

    @Override
    public List<VariableElement> getUninitializedFields(
            PackingStore store, TreePath path, boolean isStatic, Collection<? extends AnnotationMirror> receiverAnnotations) {
        boolean wasComputingUninitializedFields = computingUninitializedFields;
        computingUninitializedFields = true;

        List<VariableElement> result = super.getUninitializedFields(store, path, isStatic, receiverAnnotations);

        computingUninitializedFields = wasComputingUninitializedFields;
        return result;
    }
}
