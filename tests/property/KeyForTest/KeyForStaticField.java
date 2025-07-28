// Duplicate of test case from checker-framework
import org.checkerframework.checker.nullness.qual.*;
import java.util.HashMap;
import java.util.Map;

public class KeyForStaticField {

    public static final @KeyFor("this.map") String STATIC_KEY = "some text";

    private Map<String, Integer> map;

    public KeyForStaticField() {
        this.map = new HashMap<>();
        this.map.put(STATIC_KEY, 0);
    }

    /** Returns the value for the given key, which must be present in the map. */
    public Integer getValue(@KeyFor("this.map") String key) {
        assert this.map.containsKey(key) : "Map does not contain key " + key;
        return this.map.get(key);
    }

    public void m(KeyForStaticField other) {
        this.getValue(STATIC_KEY);
        this.getValue(STATIC_KEY);
        other.getValue(STATIC_KEY);
    }
}
