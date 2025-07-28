/* This file is part of the Property Checker. It is based on the Daikon invariant generator.
 * Copyright (c) 2021 -- present. Daikon developers & Property Checker developers.
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

package daikon;

import org.checkerframework.checker.nullness.qual.*;

// :: error: inconsistent.constructor.type
public class ListInfo {

  public Object getMyValFromParentVal(Object value) {
    Object arrayVal;

    if (value != null) {
      try {
        arrayVal = new Obj();
      // :: error: exception.parameter.invalid
      } catch (Error e) {
        throw new Exc();
      // :: error: exception.parameter.invalid
      } catch (Exception e1) {
        arrayVal = new Obj();
      }
    } else {
      arrayVal = new Obj();
    }

    // @SuppressWarnings("nullness") // We just verified (or set) arrayVal in code above.
    return arrayVal;
  }
}
