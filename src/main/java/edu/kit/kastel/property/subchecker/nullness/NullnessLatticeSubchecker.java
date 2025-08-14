package edu.kit.kastel.property.subchecker.nullness;

import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.subchecker.lattice.CooperativeChecker;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.nullness.NullnessChecker;
import org.checkerframework.checker.nullness.NullnessNoInitSubchecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.common.basetype.BaseTypeVisitor;
import org.checkerframework.framework.source.SupportedLintOptions;

import javax.annotation.processing.SupportedOptions;
import java.io.File;
import java.net.URLClassLoader;
import java.util.List;
import java.util.Set;

@SupportedLintOptions({
        NullnessChecker.LINT_NOINITFORMONOTONICNONNULL,
        NullnessChecker.LINT_REDUNDANTNULLCOMPARISON,
        // Temporary option to forbid non-null array component types, which is allowed by default.
        // Forbidding is sound and will eventually be the default.
        // Allowing is unsound, as described in Section 3.3.4, "Nullness and arrays":
        //     https://eisop.github.io/cf/manual/#nullness-arrays
        // It is the default temporarily, until we improve the analysis to reduce false positives or we
        // learn what advice to give programmers about avoid false positive warnings.
        // See issue #986: https://github.com/typetools/checker-framework/issues/986
        "soundArrayCreationNullness",
        // Old name for soundArrayCreationNullness, for backward compatibility; remove in January 2021.
        "forbidnonnullarraycomponents",
        NullnessChecker.LINT_TRUSTARRAYLENZERO,
        NullnessChecker.LINT_PERMITCLEARPROPERTY,
})
@SupportedOptions({
        "assumeKeyFor",
        "assumeInitialized",
        "jspecifyNullMarkedAlias",
        "conservativeArgumentNullnessAfterInvocation"
})
public class NullnessLatticeSubchecker extends NullnessNoInitSubchecker implements CooperativeChecker {

    private int errorCount = 0;
    private PropertyChecker parent;
    private File inputDir;

    public NullnessLatticeSubchecker(PropertyChecker parent, File inputDir) {
        this.parent = parent;
        this.inputDir = inputDir;

        setProcessingEnvironment(parent.getProcessingEnvironment());
        treePathCacher = parent.getTreePathCacher();
        setParentChecker(parent);
    }

    @Override
    public int getIdent() {
        return 0;
    }

    @Override
    public PropertyChecker getParentChecker() {
        return parent;
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        return List.of();
    }

    @Override
    public <T extends BaseTypeChecker> @Nullable T getSubchecker(Class<T> checkerClass) {
        return getParentChecker().getSubchecker(checkerClass);
    }

    @Override
    protected Set<Class<? extends BaseTypeChecker>> getImmediateSubcheckerClasses() {
        return Set.of();
    }

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        ++errorCount;
        super.reportError(source, "nullness" + "." + messageKey, args);
    }

    public File getInputDir() {
        return inputDir;
    }

    public URLClassLoader getProjectClassLoader() {
        return parent.getProjectClassLoader();
    }

    @Override
    public NullnessLatticeAnnotatedTypeFactory getTypeFactory() {
        return (NullnessLatticeAnnotatedTypeFactory) super.getTypeFactory();
    }

    @Override
    protected BaseTypeVisitor<?> createSourceVisitor() {
        return new NullnessLatticeVisitor(this);
    }

    @Override
    public NullnessLatticeVisitor getVisitor() {
        return (NullnessLatticeVisitor) super.getVisitor();
    }

    @Override
    public Lattice getLattice() {
        return getTypeFactory().getLattice();
    }

    public int getErrorCount() {
        return errorCount;
    }

    public void setErrorCount(int errorCount) {
        this.errorCount = errorCount;
    }
}
