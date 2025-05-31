package org.plumelib.util;

public class OrderedPairIterator extends java.util.Iterator {

    //@ public ghost int idx = 0;
    //@ public ghost int len;

    /*@ public normal_behavior
      @ ensures idx == 0 && len >= 0;
      @ ensures \fresh(this) && \fresh(this.*);
      @ assignable \nothing;
      @*/
    public OrderedPairIterator(java.util.Iterator i1, java.util.Iterator i2, java.util.Comparator c);

    /*@ public normal_behavior
      @ ensures \result == (idx < len);
      @ assignable \strictly_nothing;
      @*/
    public /*@helper@*/ boolean hasNext();

    /*@ public normal_behavior
      @ requires (idx < len);
      @ ensures idx == \old(idx) + 1;
      @ ensures \result.first != null || \result.second != null;
      @ assignable idx;
      @*/
    public /*@helper@*/ MPair next();
}
