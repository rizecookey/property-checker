package edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual;

import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@DefaultQualifierInHierarchy
@SubtypeOf({})
public @interface TopEmpty {
}
