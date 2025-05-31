package java.io;

public class InputStream {

    //@ public ghost \seq seq;
    protected /*@spec_public@*/ int pos;

    //@ public ghost \locset footprint;
    //@ public invariant \subset(this.*, footprint);
    //@ public invariant 0 <= pos && pos <= seq.length;
    //@ public accessible \inv: footprint;

    /*@ public normal_behavior
      @ requires 0 <= offset;
      @ requires length <= buf.length - offset;
      @ requires length + pos <= seq.length;
      @ requires \dl_array2seq(buf)[0 .. offset] == seq[pos - offset .. pos];
      @ ensures 0 <= \result && \result <= length;
      @ ensures \dl_array2seq(buf)[0 .. offset + \result] == seq[\old(pos) - offset .. pos];
      @ ensures pos == \old(pos) + \result;
      @ assignable buf[offset .. offset + length], pos;
      @*/
    public int read(byte[] buf, int offset, int length);

    /*@ public normal_behavior
      @ ensures \result == pos;
      @ assignable \strictly_nothing;
      @*/
    public int pos();

    /*@ public normal_behavior
      @ ensures \result == seq.length;
      @ assignable \strictly_nothing;
      @*/
    public int length();
}
