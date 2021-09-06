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

import edu.kit.iti.checker.property.subchecker.lattice.case_study_qual.*;
import edu.kit.iti.checker.property.checker.qual.*;

public class InvariantInfo {

  public final @Nullable String vars;

  // :: error: inconsistent.constructor.type
  public InvariantInfo(@Nullable String vars) {
    this.vars = vars;
  }

  @JMLClause("ensures \result == vars")
  @JMLClause("assignable \\nothing")
  public @Nullable String vars() {
    return this.vars;
  }

  @JMLClause("ensures \result == null <==> vars == null")
  @JMLClause("assignable \\nothing")
  public @Nullable List var_permutations() {
    if (vars == null) {
      return null;
    }

    return new ArrayList();
  }
}
