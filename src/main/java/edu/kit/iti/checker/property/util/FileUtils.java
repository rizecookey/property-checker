/* This file is part of the Property Checker.
 * Copyright (c) 2021 -- present. Property Checker developers.
 *
 * This program is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details.
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 */
package edu.kit.iti.checker.property.util;

import java.io.BufferedWriter;
import java.io.File;
import java.io.FileWriter;
import java.io.IOException;

public final class FileUtils {

    private FileUtils() { }

    public static void createFile(File f) {
        try {
            if (f.getParentFile() != null) {
                f.getParentFile().mkdirs();
            }
            f.createNewFile();
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }

    public static void writeToFile(File f, String s) {
        try {
            createFile(f);

            BufferedWriter writer;
            writer = new BufferedWriter(new FileWriter(f));
            writer.write(s);
            writer.close();
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }
    }
}
