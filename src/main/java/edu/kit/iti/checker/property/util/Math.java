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

public final class Math {

    private Math() { }

    public static int gcd(int a, int b) {
        if (b < a) {
            int temp = a;
            a = b;
            b = temp;
        }

        while (b != 0) {
            int temp = b;
            b = java.lang.Math.floorMod(a, b);
            a = temp;
        }

        return a;
    }

    public static int eea0(int a, int b) {
        if (b < a) {
            int temp = a;
            a = b;
            b = temp;
        }

        int oldR = a;
        int r = b;
        int oldS = 1;
        int s = 0;
        int oldT = 0;
        int t = 1;

        while (r != 0) {
            int quot = oldR / r;

            int temp = r;
            r = oldR - quot * r;
            oldR = temp;

            temp = s;
            s = oldS - quot * s;
            oldS = temp;

            temp = t;
            t = oldT -quot * t;
            oldT = temp;
        }

        return oldS;
    }

    public static int eea1(int a, int b) {
        if (b < a) {
            int temp = a;
            a = b;
            b = temp;
        }

        int oldR = a;
        int r = b;
        int oldS = 1;
        int s = 0;
        int oldT = 0;
        int t = 1;

        while (r != 0) {
            int quot = oldR / r;

            int temp = r;
            r = oldR - quot * r;
            oldR = temp;

            temp = s;
            s = oldS - quot * s;
            oldS = temp;

            temp = t;
            t = oldT -quot * t;
            oldT = temp;
        }

        return oldT;
    }

    public static int lcm(int a, int b) {
        return a * b / gcd(a, b);
    }

    public static int mcd(int n, int m, int a, int b) {
        for (int d = gcd(n, m); true; --d) {
            if (m % d == 0 && n % d == 0 && java.lang.Math.floorMod(a, d) == java.lang.Math.floorMod(b, d)) {
                return d;
            }
        }
    }
}
