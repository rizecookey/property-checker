package edu.kit.kastel.property.packing.qual;

import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;
import org.checkerframework.framework.qual.QualifierArgument;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  UnknownInitialization.class)
@Repeatable(EnsuresUnknownInit.List.class)
public @interface EnsuresUnknownInit {

    String[] value() default {"this"};

    @QualifierArgument("value")
    Class<?> targetValue();

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = UnknownInitialization.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresUnknownInit[] value();
    }
}
