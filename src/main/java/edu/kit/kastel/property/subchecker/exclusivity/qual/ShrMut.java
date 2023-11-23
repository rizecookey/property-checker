package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Object may be mutated and reference can be copied without restriction.
 * Mutable aliases to the same object might exist.
 *
 * <p>This is the default type, so programmers usually do not need to write it.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({ReadOnly.class})
@DefaultQualifierInHierarchy
public @interface ShrMut {}
