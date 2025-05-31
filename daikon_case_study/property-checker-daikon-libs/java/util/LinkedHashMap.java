package java.util;

public final class LinkedHashMap extends HashMap {
	
    /*@ public normal_behavior
      @ ensures key_seq.length == 0;
      @ ensures value_seq.length == 0;
      @ assignable \nothing;
      @*/
    public LinkedHashMap();
}
