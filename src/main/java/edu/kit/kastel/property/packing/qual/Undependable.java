package edu.kit.kastel.property.packing.qual;

import org.checkerframework.framework.qual.DefaultQualifierInHierarchy;
import org.checkerframework.framework.qual.SubtypeOf;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * An undependable field is one that never appears in a dependent type. Undependable fields can be reassigned even
 * if their receiver is packed or aliased.
 *
 * TODO: This is currently a trusted default annotation.
 */
@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({})
@DefaultQualifierInHierarchy
public @interface Undependable {
}
