package edu.kit.kastel.property.subchecker.exclusivity.qual;

import org.checkerframework.checker.initialization.qual.HoldsForDefaultValue;
import org.checkerframework.framework.qual.*;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;


@Retention(RetentionPolicy.RUNTIME)
@Target({ElementType.TYPE_USE})
@SubtypeOf({ReadOnly.class})
@DefaultQualifierInHierarchy
@DefaultFor(
        value={TypeUseLocation.LOCAL_VARIABLE, TypeUseLocation.ALL})
@HoldsForDefaultValue
public @interface MaybeAliased {}
