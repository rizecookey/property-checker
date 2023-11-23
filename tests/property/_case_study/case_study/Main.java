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
package case_study;

import edu.kit.kastel.property.subchecker.lattice.case_study_qual.*;
import edu.kit.kastel.property.checker.qual.*;

public class Main {

    // :: error: inconsistent.constructor.type
    private Main() { }
    
    public static void main(String[] args) {
        // :: error: assignment.type.incompatible
        @AllowedFor(age="18") Product product18 = new Product("Louisiana Buzzsaw Carnage", 10, 18);
        // :: error: assignment.type.incompatible
        @AllowedFor(age="6") Product product6 = new Product("Tim & Jeffrey, All Episodes", 10, 6);
        
        Customer customer18 = new Customer("Alice", 18);
        Customer customer14 = new Customer("Bob", 14);
        
        //Customer customer6 = new Customer("Charlie", 6);

        // :: error: argument.type.incompatible
        customer18.order(product18);
        // :: error: argument.type.incompatible
        customer18.order(product6);
        
        //customer14.order(product18);
        
        // :: error: argument.type.incompatible
        customer14.order(product6);
        
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        
        Shop.getInstance().processNextOrder();
    }
}
