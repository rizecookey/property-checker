package edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual;

import org.checkerframework.framework.qual.InheritedAnnotation;
import org.checkerframework.framework.qual.PostconditionAnnotation;
import org.checkerframework.framework.qual.QualifierArgument;

import java.lang.annotation.*;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@InheritedAnnotation
@PostconditionAnnotation(qualifier =  edu.kit.kastel.property.subchecker.lattice.qual.Length.class)
@Repeatable(EnsuresLength.List.class)
public @interface EnsuresLength {

    String[] value() default {"this"};

    @QualifierArgument("len")
    String len();

    @Documented
    @Retention(RetentionPolicy.RUNTIME)
    @Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
    @PostconditionAnnotation(qualifier = Length.class)
    @InheritedAnnotation
    public static @interface List {

        EnsuresLength[] value();
    }
}
