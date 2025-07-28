package org.plumelib.util;

public class FilesPlume {

    public static boolean canCreateAndWrite(java.io.File f);

    public static void writeObject(Object o, java.io.File f);

    public static Object readObject(java.io.File f);
}
