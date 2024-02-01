package edu.kit.kastel.property.packing.qual;

import edu.kit.kastel.property.subchecker.exclusivity.qual.ReadOnly;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  ReadOnly.class)
@Repeatable(EnsuresInitialized.List.class)
public @interface EnsuresInitialized {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = ReadOnly.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresInitialized[] value();
    }
}
