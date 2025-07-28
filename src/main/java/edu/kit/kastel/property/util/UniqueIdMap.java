package edu.kit.kastel.property.util;

import java.util.HashMap;
import java.util.Map;

public class UniqueIdMap<T> {

    private final Map<T, Long> map;
    private long nextUid;

    public UniqueIdMap() {
        map = new HashMap<>();
        nextUid = 0;
    }

    public long getId(T object) {
        return map.computeIfAbsent(object, o -> nextUid++);
    }

    @Override
    public String toString() {
        return map.toString();
    }
}
