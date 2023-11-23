package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Object may not be mutatded and the reference may only be copied as {@link ReadOnly}.
 * In contrast to {@link ShrMut}, a property about the object may be asserted.
 * Any active alias to the same object is at most {@link Immutable}.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({ReadOnly.class})
public @interface Restricted {}
