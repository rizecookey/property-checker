package edu.kit.kastel.property.packing.qual;

import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A monotonic method respects the constraints of the freedom-before-commitment type system.
 *
 * <p> In a monotonic method, every field assignment must respect the declared type of that field, and the assigned
 *  field must be {@link Undependable}.
 *  Also, no non-monotonic methods may be called.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.METHOD, ElementType.CONSTRUCTOR})
@SubtypeOf({NonMonotonic.class})
@DefaultQualifierInHierarchy
public @interface Monotonic {
}
