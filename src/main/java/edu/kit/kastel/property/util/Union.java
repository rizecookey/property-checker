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

import java.util.function.Consumer;
import java.util.function.Function;

public final class Union<S, L extends S, R extends S> {

    public static <S, L extends S, R extends S> Union<S,L,R> left(L left) {
        if (left == null) {
            throw new IllegalArgumentException();
        }

        Union<S,L,R> union = new Union<>();
        union.left = left;
        return union;
    }

    public static <S, L extends S, R extends S> Union<S,L,R> right(R right) {
        if (right == null) {
            throw new IllegalArgumentException();
        }

        Union<S,L,R> union = new Union<>();
        union.right = right;
        return union;
    }

    private L left;
    private R right;

    private Union() { }

    public S get() {
        return left == null ? right : left;
    }

    public L getLeft() {
        return left;
    }

    public R getRight() {
        return right;
    }

    public void consume(Consumer<L> consumeLeft, Consumer<R> consumeRight) {
        if (left != null) {
            consumeLeft.accept(left);
        } else {
            consumeRight.accept(right);
        }
    }

    public <NS, NL extends NS, NR extends NS> Union<NS,NL,NR> map(Function<L,NL> mapLeft, Function<R,NR> mapRight) {
        if (left != null) {
            return left(mapLeft.apply(left));
        } else {
            return right(mapRight.apply(right));
        }
    }
}
