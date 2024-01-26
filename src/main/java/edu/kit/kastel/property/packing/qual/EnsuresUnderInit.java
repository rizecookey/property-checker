package edu.kit.kastel.property.packing.qual;

import org.checkerframework.checker.initialization.qual.UnderInitialization;
import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;
import org.checkerframework.framework.qual.QualifierArgument;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  UnderInitialization.class)
@Repeatable(EnsuresUnderInit.List.class)
public @interface EnsuresUnderInit {

    String[] value() default {"this"};

    @QualifierArgument("value")
    Class<?> targetValue();

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = UnderInitialization.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresUnderInit[] value();
    }
}
