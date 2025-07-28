package java.io;

public class PrintStream extends java.io.FilterOutputStream {

    public PrintStream(java.io.OutputStream out);
    public PrintStream(java.io.OutputStream out, boolean autoFlush);

    public void print(boolean b);
    public void print(char c);
    public void print(int i);
    public void print(long l);
    // public void print(float f);
    // public void print(double d);
    public void print(char[] s);
    public void print(java.lang.String s);
    public void print(java.lang.Object obj);
    public void printf(java.lang.String s, Object... args);
    public void println();
    public void println(boolean x);
    public void println(char x);
    public void println(int x);
    public void println(long x);
    // public void println(float x);
    // public void println(double x);
    public void println(char[] x);
    public void println(java.lang.String x);
    public void __println_trampoline(String x, boolean b0, boolean b1);
    public void println(java.lang.Object x);
    public void __println_trampoline(java.lang.Object x, boolean b0, boolean b1);
}
