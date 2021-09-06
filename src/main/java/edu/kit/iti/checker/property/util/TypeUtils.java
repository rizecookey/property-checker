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

import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import com.sun.tools.javac.code.Type;
import com.sun.tools.javac.code.Type.ArrayType;

public final class TypeUtils {

    private TypeUtils() { }

    @SuppressWarnings("nls")
    public static String unannotatedTypeName(AnnotatedTypeMirror mirror) {
        if (mirror instanceof AnnotatedExecutableType) {
            throw new IllegalArgumentException();
        }

        if (mirror.getUnderlyingType() instanceof ArrayType) {
            return ((ArrayType) mirror.getUnderlyingType()).elemtype.asElement().toString() + "[]";
        } else {
            return ((Type) mirror.getUnderlyingType()).asElement().toString();
        }
    }
}
