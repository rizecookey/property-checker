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
import java.util.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;

interface MultiInheritanceA {
    
    @Length(min="1", max="3") List foo(@Length(min="0", max="99") List a);
}

interface MultiInheritanceB {
    
    @Length(min="2", max="3") List foo(@Length(min="0", max="199") List a);
}

interface MultiInheritanceC {
    
    @Length(min="1", max="2") List foo(@Length(min="0", max="299") List a);
}

abstract class A implements MultiInheritanceA, MultiInheritanceB, MultiInheritanceC {

    public abstract @Length(min="2", max="2") List foo(@Length(min="0", max="299") List a);
}

abstract class B implements MultiInheritanceA, MultiInheritanceB, MultiInheritanceC {

    // :: error: override.return.invalid :: error: override.param.invalid
    public abstract @Length(min="1", max="3") List foo(@Length(min="0", max="99") List a);
}
