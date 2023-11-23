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

public class IntWFTest {
    // :: error: initialization.fields.uninitialized
    public IntWFTest() {}
    
    @Interval(min="1", max="3") int wellFormedInterval0;
    @Interval(min="1", max="1") int wellFormedInterval1;
    
    // :: error: type.invalid
    @Interval(min="1", max="0") int malFormedInterval0;
    
    // :: error: type.invalid
    @Interval(min="1", max="2") long malFormedInterval1;
    
    // :: error: type.invalid
    @Interval(min="1", max="2") String malFormedInterval2;
        
    @Remainder(remainder="1", modulus="6") int wellFormedModulus0;
    @Remainder(remainder="0", modulus="6") int wellFormedModulus1;
    @Remainder(remainder="0", modulus="1") int wellFormedModulus2;
    
    // :: error: type.invalid
    @Remainder(remainder="0", modulus="0") int malFormedModulus0;
    // :: error: type.invalid
    @Remainder(remainder="1", modulus="1") int malFormedModulus1;
    // :: error: type.invalid
    @Remainder(remainder="2", modulus="1") int malFormedModulus2;
    // :: error: type.invalid
    @Remainder(remainder="2", modulus="2") int malFormedModulus3;
    // :: error: type.invalid
    @Remainder(remainder="3", modulus="2") int malFormedModulus4;
    
}
