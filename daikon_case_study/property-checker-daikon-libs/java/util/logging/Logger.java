package java.util.logging;

public class Logger {

    public static Logger getLogger(String s);

    /*@ public normal_behavior
      @ assignable \nothing; */
    public /*@helper@*/ boolean isLoggable(Level l);

    public void all(Object obj);
    public void config(Object obj);
    /*@ public normal_behavior
      @ assignable \nothing; */
    public /*@helper@*/ void fine(Object obj);
    public void finer(Object obj);
    public void finest(Object obj);
    public void info(Object obj);
    public void off(Object obj);
    public void severe(Object obj);
    public void warning(Object obj);
}
