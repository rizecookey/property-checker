package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.*;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  Unique.class)
@Repeatable(EnsuresUnique.List.class)
public @interface EnsuresUnique {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = Unique.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresUnique[] value();
    }
}
