package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Object may not be mutated and naturally only be copied as {@link ReadOnly}.
 * Aliases to the same object may be of any type, even {@link ExclusivityBottom}.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE, ElementType.TYPE_PARAMETER})
@SubtypeOf({})
public @interface ReadOnly {}
