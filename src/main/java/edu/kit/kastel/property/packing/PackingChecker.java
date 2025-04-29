package edu.kit.kastel.property.packing;

import edu.kit.kastel.property.config.Config;
import org.apache.commons.io.FileUtils;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.initialization.InitializationChecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SupportedOptions;
import org.checkerframework.javacutil.InternalUtils;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.*;
import java.util.stream.Collectors;

@SupportedOptions({
        Config.INPUT_DIR_OPTION,
        "assumeInitialized"
})
public abstract class PackingChecker extends InitializationChecker {

    private URLClassLoader projectClassLoader;

    @Override
    public final Class<? extends BaseTypeChecker> getTargetCheckerClass() {
        List<BaseTypeChecker> targets = getTargetCheckers();
        if (targets.size() == 1) {
            return targets.get(0).getClass();
        }

        throw new UnsupportedOperationException("This packing checker has multiple targets!");
    }

    public abstract List<BaseTypeChecker> getTargetCheckers();

    @Override
    public NavigableSet<String> getSuppressWarningsPrefixes() {
        NavigableSet<String> result = super.getSuppressWarningsPrefixes();
        result.add("packing");
        return result;
    }

    @Override
    public void reportError(@Nullable Object source, @CompilerMessageKey String messageKey, Object... args) {
        super.reportError(source, messageKey, args);
    }

    @Override
    public PackingAnnotatedTypeFactory getTypeFactory() {
        return (PackingAnnotatedTypeFactory) super.getTypeFactory();
    }

    @Override
    protected PackingVisitor createSourceVisitor() {
        // Don't load the visitor reflexively based on checker class name.
        // Instead, always use the PackingVisitor.
        return new PackingVisitor(this);
    }

    public String getInputDir() {
        return getOptionsNoSubcheckers().get(Config.INPUT_DIR_OPTION);
    }

    @SuppressWarnings("nls")
    public URLClassLoader getProjectClassLoader() {
        if (projectClassLoader == null) {
            try {
                File projectClasses = new File(getInputDir());

                JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
                StandardJavaFileManager fileManager = compiler.getStandardFileManager(null, null, null);
                @SuppressWarnings({ "unchecked" })
                Iterable<? extends JavaFileObject> src = fileManager.getJavaFileObjectsFromFiles(
                        FileUtils.listFiles(projectClasses, new String[] {"java"}, true));

                ClassLoader currentClassLoader = InternalUtils.getClassLoaderForClass(getClass());
                String sep = System.getProperty("path.separator");
                String classPathStr = System.getProperty("java.class.path") + sep + projectClasses.toURI().toURL();

                if (currentClassLoader instanceof URLClassLoader) {
                    classPathStr +=
                            sep
                                    + Arrays.stream(((URLClassLoader) currentClassLoader).getURLs()).map(URL::toString).collect(Collectors.joining(sep));
                }

                JavaCompiler.CompilationTask task = compiler.getTask(null, fileManager, null,
                        Arrays.asList("-classpath", classPathStr),
                        null, src);
                task.call();

                projectClassLoader = new URLClassLoader(new URL[] {projectClasses.toURI().toURL()}, currentClassLoader);
            } catch (IOException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }

        return projectClassLoader;
    }
}
