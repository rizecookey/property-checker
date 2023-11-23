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

import edu.kit.kastel.property.subchecker.lattice.case_study_qual.*;
import edu.kit.kastel.property.checker.qual.*;

public class ArrayList implements List {
	

	@JMLClause("assignable \\nothing")
	// :: error: inconsistent.constructor.type
	public ArrayList() {}
}