package edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier = UnknownHeapProperty.class)
@Repeatable(EnsuresUnknownHeapProperty.List.class)
public @interface EnsuresUnknownHeapProperty {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = UnknownHeapProperty.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresUnknownHeapProperty[] value();
    }
}
