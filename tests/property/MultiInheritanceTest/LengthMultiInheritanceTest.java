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
    
    @Length(len="1") List foo(@Length(len="0") List a);
}

interface MultiInheritanceB {
    
    @Length(len="2") List foo(@Length(len="0") List a);
}

abstract class A implements MultiInheritanceA {

    public abstract @Length(len="1") List foo(@Length(len="0") List a);
}

abstract class B implements MultiInheritanceA, MultiInheritanceB {

    // :: error: length.override.return.invalid :: error: length.override.param.invalid
    public abstract @Length(len="1") List foo(@Length(len="0") List a);
}
