package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.SubtypeOf;
import org.checkerframework.framework.qual.TypeUseLocation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Object may be mutated, but the reference may only be copied as {@link ReadOnly}.
 * Any alias to the same object ist at most {@link ReadOnly}.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({Restricted.class})
@DefaultFor({TypeUseLocation.CONSTRUCTOR_RESULT})
public @interface ExclMut {}
