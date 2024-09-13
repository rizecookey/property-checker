package edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier = NonEmptyDoublyLinked.class)
@Repeatable(EnsuresNonEmptyDoublyLinked.List.class)
public @interface EnsuresNonEmptyDoublyLinked {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = NonEmptyDoublyLinked.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresNonEmptyDoublyLinked[] value();
    }
}
