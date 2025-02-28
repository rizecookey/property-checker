package edu.kit.kastel.property.subchecker.lattice;

import edu.kit.kastel.property.lattice.Checkable;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.lattice.compiler.ClassBuilder;
import edu.kit.kastel.property.util.ClassUtils;

import java.util.Arrays;
import java.util.List;
import java.util.function.Function;

public interface CooperativeAnnotatedTypeFactory {

    CooperativeChecker getChecker();

    default <T extends Checkable> void setCheckerMethods(List<T> checkables, String className, Function<T, String> methodName) {
        ClassBuilder compiler = new ClassBuilder(className + getChecker().getIdent());

        for (T chk : checkables) {
            Class<?>[] paramTypes = chk.getParameterTypes();

            addMethods_label:
            if (paramTypes.length > 0 && paramTypes[0] == null) {
                // null represents the any type, so we add a method for Object and all primitives.

                paramTypes[0] = Object.class;
                compiler.addMethod(
                        methodName.apply(chk),
                        chk.getCondition(),
                        Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                        chk.getParameterNames(),
                        chk.toString());

                // Don't add methods for primitives for NonNull
                if (chk instanceof PropertyAnnotationType.PropertyCheckable propChk && propChk.getPropertyAnnotationType().isNonNull()) {
                    break addMethods_label;
                }

                for (Class<?> primitive : ClassUtils.PRIMITIVES) {
                    paramTypes[0] = primitive;
                    compiler.addMethod(
                            methodName.apply(chk),
                            chk.getCondition(),
                            Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                            chk.getParameterNames(),
                            chk.toString());
                }
            } else {
                compiler.addMethod(
                        methodName.apply(chk),
                        chk.getCondition(),
                        Arrays.stream(paramTypes).map(Class::getCanonicalName).toArray(String[]::new),
                        chk.getParameterNames(),
                        chk.toString());
            }
        }

        Class<?> cls = compiler.compile(getChecker().getProjectClassLoader());

        if (cls == null) {
            return;
        }

        for (T chk : checkables) {
            try {
                Class<?>[] paramTypes = chk.getParameterTypes();

                if (paramTypes.length > 0 && paramTypes[0] == null) {
                    paramTypes[0] = Object.class;
                }

                chk.setCheckerMethod(cls.getMethod(methodName.apply(chk), paramTypes));
            } catch (NoSuchMethodException | SecurityException e) {
                e.printStackTrace();
                System.exit(1);
            }
        }
    }
}
