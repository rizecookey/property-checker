package java.io;

public class OutputStream {

    //@ public ghost \seq seq;
    protected /*@spec_public@*/ int pos;

    //@ public ghost \locset footprint;
    //@ public invariant \subset(this.*, footprint);
    //@ public invariant pos == seq.length;
    //@ public accessible \inv: footprint;

    /*@ public normal_behavior
      @ requires 0 <= offset && offset < buf.length;
      @ requires length <= buf.length - offset;
      @ ensures seq == \seq_concat(\old(seq), \dl_array2seq(buf)[offset .. offset + length]);
      @ ensures pos == \old(pos) + length;
      @ ensures \new_elems_fresh(this.footprint);
      @ assignable this.footprint;
      @*/
    public void write(byte[] buf, int offset, int length);

    /*@ public normal_behavior
      @ ensures seq == \seq_concat(\old(seq), \dl_array2seq(buf));
      @ ensures pos == \old(pos) + buf.length;
      @ ensures \new_elems_fresh(this.footprint);
      @ assignable this.footprint;
      @*/
    public void write(byte[] buf);

    /*@ public normal_behavior
      @ ensures \dl_array2seq(\result) == seq;
      @ assignable \strictly_nothing;
      @*/
    public byte[] toByteArray();
}
