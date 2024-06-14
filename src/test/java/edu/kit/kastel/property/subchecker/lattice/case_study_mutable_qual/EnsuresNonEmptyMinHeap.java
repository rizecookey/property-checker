package edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier = NonEmptyMinHeap.class)
@Repeatable(EnsuresNonEmptyMinHeap.List.class)
public @interface EnsuresNonEmptyMinHeap {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = NonEmptyMinHeap.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresNonEmptyMinHeap[] value();
    }
}
