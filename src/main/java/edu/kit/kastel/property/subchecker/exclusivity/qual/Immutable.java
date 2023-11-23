package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * Object may not be mutated, but the reference may be copied without restriction.
 * Any alias to the same object is at most {@link Immutable}.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({Restricted.class})
@DefaultFor(types={
        byte.class,
        short.class,
        int.class,
        long.class,
        float.class,
        double.class,
        boolean.class,
        char.class,
        String.class})
public @interface Immutable {}
