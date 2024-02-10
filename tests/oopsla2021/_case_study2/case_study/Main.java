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
        @AllowedFor(age="18") Product product18 = Product.product18("Louisiana Buzzsaw Carnage", 10);
        @AllowedFor(age="6") Product product6 = Product.product6("Tim & Jeffrey, All Episodes", 10);
        
        @AgedOver(age="18") Customer customer18 = Customer.customer18("Alice");
        @AgedOver(age="14") Customer customer14 = Customer.customer14("Bob");
        
        addOrder18(customer18, product18);
        addOrder14(customer18, product6);
        addOrder14(customer14, product6);
        
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        Shop.getInstance().processNextOrder();
        
        Shop.getInstance().processNextOrder();
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public static void addOrder18(@AgedOver(age="18") Customer customer, @AllowedFor(age="18") Product product) {
        Shop.getInstance().addOrder(Order.order18(customer, product));
    }

    @JMLClauseTranslationOnly("assignable Shop.instance.orders")
    public static void addOrder14(@AgedOver(age="14") Customer customer, @AllowedFor(age="14") Product product) {
        Shop.getInstance().addOrder(Order.order14(customer, product));
    }
}
