package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  ReadOnly.class)
@Repeatable(EnsuresReadOnly.List.class)
public @interface EnsuresReadOnly {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = ReadOnly.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresReadOnly[] value();
    }
}
