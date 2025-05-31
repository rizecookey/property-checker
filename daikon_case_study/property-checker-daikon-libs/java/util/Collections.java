package java.util;

public class Collections {

    /*@ public normal_behavior
      @ assignable col.seq;
      @*/
    public static void sort(Collection col, Comparator com);
}
