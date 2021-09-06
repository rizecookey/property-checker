/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.iti.checker.property.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;
import java.util.function.UnaryOperator;

public final class CollectionUtils {

    private CollectionUtils() { }

    public static <K,E> void addToListMap(Map<K, List<E>> map, K key, E elem) {
        addToCollectionMap(map, key, elem, ArrayList<E>::new);
    }

    public static <K,E> void addToSetMap(Map<K, Set<E>> map, K key, E elem) {
        addToCollectionMap(map, key, elem, HashSet<E>::new);
    }

    public static <K, E, C extends Collection<E>> void addToCollectionMap(Map<K, C> map, K key, E elem, Supplier<C> supplier) {
        if (!map.containsKey(key)) {
            map.put(key, supplier.get());
        }

        map.get(key).add(elem);
    }

    public static <K,E> List<E> getUnmodifiableList(Map<K, List<E>> map, K key) {
        return getUnmodifiableElement(map, key, Collections::unmodifiableList, Collections.emptyList());
    }

    public static <K,E> Set<E> getUnmodifiableSet(Map<K, Set<E>> map, K key) {
        return getUnmodifiableElement(map, key, Collections::unmodifiableSet, Collections.emptySet());
    }

    public static <K, E> E getUnmodifiableElement(Map<K, E> map, K key, UnaryOperator<E> makeUnmodifiable, E defaultElement) {
        return map.containsKey(key)
                ? makeUnmodifiable.apply(map.get(key))
                : defaultElement;
    }
}
