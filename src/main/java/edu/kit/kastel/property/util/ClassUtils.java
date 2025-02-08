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

import edu.kit.kastel.property.packing.PackingChecker;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.type.DeclaredType;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;

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

    public static TypeMirror typeForName(String str, PackingFieldAccessSubchecker checker) {
        return typeForName(str, checker.getPackingChecker());
    }

    @SuppressWarnings("nls")
    public static TypeMirror typeForName(String str, LatticeSubchecker checker) {
        return typeForName(str, checker.getParentChecker());
    }

    public static TypeMirror typeForName(String str, PackingChecker checker) {
        var types = checker.getTypeUtils();
        return switch (str) {
            case "boolean" -> types.getPrimitiveType(TypeKind.BOOLEAN);
            case "byte" -> types.getPrimitiveType(TypeKind.BYTE);
            case "char" -> types.getPrimitiveType(TypeKind.CHAR);
            case "int" -> types.getPrimitiveType(TypeKind.INT);
            case "short" -> types.getPrimitiveType(TypeKind.SHORT);
            case "long" -> types.getPrimitiveType(TypeKind.LONG);
            case "float" -> types.getPrimitiveType(TypeKind.FLOAT);
            case "double" -> types.getPrimitiveType(TypeKind.DOUBLE);
            case "void" -> types.getNoType(TypeKind.VOID);
            case "any" -> null;
            case "<nulltype>" -> null;
            default -> {
                var type = checker.getElementUtils().getTypeElement(str).asType();
                if (type == null) {
                    throw new AssertionError(str);
                }
                yield type;
            }
        };
    }

    public static Class<?> classForName(String name, LatticeSubchecker checker) {
        try {
            return Class.forName(name);
        } catch (ClassNotFoundException e) {
            try {
                return checker.getProjectClassLoader().loadClass(name);
            } catch (ClassNotFoundException e1) {
                e1.printStackTrace();
                throw new AssertionError(name);
            }
        }
    }

    public static Class<?> literalKindToClass(Kind kind) {
        return switch (kind) {
            case BOOLEAN_LITERAL -> boolean.class;
            case CHAR_LITERAL -> char.class;
            case INT_LITERAL -> int.class;
            case LONG_LITERAL -> long.class;
            case FLOAT_LITERAL -> float.class;
            case DOUBLE_LITERAL -> double.class;
            default -> null;
        };
    }

    public static String getCanonicalName(TypeMirror type) {
        if (type == null) {
            return null;
        }
        if (type.getKind().isPrimitive()) {
            return TypesUtils.simpleTypeName(type);
        } else if (type instanceof DeclaredType dt) {
            return TypesUtils.getQualifiedName(dt);
        }
        return null;
    }
}
