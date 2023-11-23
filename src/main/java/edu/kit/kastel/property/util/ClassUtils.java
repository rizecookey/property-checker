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
package edu.kit.kastel.property.util;

import com.sun.source.tree.Tree.Kind;

import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;

public final class ClassUtils {

    private ClassUtils() { }

    public static final Class<?>[] PRIMITIVES = new Class<?>[] {
        boolean.class,
        byte.class,
        char.class,
        int.class,
        short.class,
        long.class,
        float.class,
        double.class
    };

    @SuppressWarnings("nls")
    public static String classNameToFileName(String className) {
        return className.replace('.', '/') + ".java";
    }

	public static String fileNameToClassName(String fileName) {
        fileName = fileName.substring(0, fileName.lastIndexOf('.')); 
        fileName = fileName.replace('/', '.');
        return fileName;
        
	}

    @SuppressWarnings("nls")
    public static Class<?> classOrPrimitiveForName(String str, LatticeSubchecker checker) {
        switch(str) {
        case "boolean": return boolean.class;
        case "byte": return byte.class;
        case "char": return char.class;
        case "int": return int.class;
        case "short": return short.class;
        case "long": return long.class;
        case "float": return float.class;
        case "double": return double.class;
        case "void": return void.class;
        case "any": return null;
        case "<nulltype>": return null;
        default: try {
                return Class.forName(str);
            } catch (ClassNotFoundException e) {
                try {
                    return checker.getProjectClassLoader().loadClass(str);
                } catch (ClassNotFoundException e1) {
                    e1.printStackTrace();
                    throw new AssertionError(str);
                }
            }
        }
    }

    public static Class<?> literalKindToClass(Kind kind) {
        switch(kind) {
        case BOOLEAN_LITERAL: return boolean.class;
        case CHAR_LITERAL: return char.class;
        case INT_LITERAL: return int.class;
        case LONG_LITERAL: return long.class;
        case FLOAT_LITERAL: return float.class;
        case DOUBLE_LITERAL: return double.class;
        default: return null;
        }
    }
}
