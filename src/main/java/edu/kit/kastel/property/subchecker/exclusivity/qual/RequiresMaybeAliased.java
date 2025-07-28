package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PreconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PreconditionAnnotation(qualifier =  MaybeAliased.class)
@Repeatable(RequiresMaybeAliased.List.class)
public @interface RequiresMaybeAliased {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PreconditionAnnotation(qualifier = MaybeAliased.class)
    @InheritedAnnotation
    public static @interface List {

        RequiresMaybeAliased[] value();
    }
}
