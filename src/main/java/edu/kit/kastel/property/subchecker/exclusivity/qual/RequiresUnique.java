package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PreconditionAnnotation;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PreconditionAnnotation(qualifier =  Unique.class)
@Repeatable(RequiresUnique.List.class)
public @interface RequiresUnique {

    String[] value() default {"this"};

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PreconditionAnnotation(qualifier = Unique.class)
    @InheritedAnnotation
    public static @interface List {

        RequiresUnique[] value();
    }
}
