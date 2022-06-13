import org.checkerframework.checker.nullness.qual.*;

public class Test {
    
    public static @NonNull Object bar(@Nullable Object arg) {
        Object local = null;
        if (arg != null) {
            local = arg;
            arg = null;
            local = arg;
            // :: error: return.type.incompatible
            return local;
        }
        return new Object();
    }
}
