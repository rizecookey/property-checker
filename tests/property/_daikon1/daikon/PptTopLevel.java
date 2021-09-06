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

// :: error: inconsistent.constructor.type
public class PptTopLevel {

	public boolean is_less_equal(VarInfo v1, VarInfo v2) {
		Invariant inv = null;
		PptSlice slice = null;

		slice = findSlice(v1, v2);
		if (slice != null) {
			// :: error: argument.type.incompatible
			inv = instantiate(slice);
		}

		// :: error: argument.type.incompatible :: error: method.invocation.invalid
		return (inv != null) && slice.is_inv_true(inv);
	}


	public @Nullable PptSlice findSlice(VarInfo v1, VarInfo v2) { return null; }
	public @Nullable Invariant instantiate(PptSlice slice) { return null; }
}

// :: error: inconsistent.constructor.type
class VarInfo { }
// :: error: inconsistent.constructor.type
class Invariant { }
// :: error: inconsistent.constructor.type
class PptSlice {
	
	public boolean is_inv_true(Invariant inv) { return true; }
}
