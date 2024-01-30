package edu.kit.kastel.property.util;

import org.checkerframework.dataflow.qual.Pure;

public final class Packing {

    private Packing() { }

    @Pure
    public static <T> void pack(T t, Class<? super T> as) {}

    @Pure
    public static <T> void unpack(T t, Class<? super T> from) {}
}
