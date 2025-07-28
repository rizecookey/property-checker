package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.framework.qual.DefaultFor;
import org.checkerframework.framework.qual.SubtypeOf;
import org.checkerframework.framework.qual.TypeKind;
import org.checkerframework.framework.qual.TypeUseLocation;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({MaybeAliased.class})
@DefaultFor(
        value={TypeUseLocation.CONSTRUCTOR_RESULT},
        typeKinds={TypeKind.BOOLEAN, TypeKind.BYTE, TypeKind.CHAR, TypeKind.INT, TypeKind.SHORT, TypeKind.LONG, TypeKind.DOUBLE, TypeKind.FLOAT, TypeKind.NULL})
public @interface Unique {}
