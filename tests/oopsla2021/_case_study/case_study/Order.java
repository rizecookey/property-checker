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

public class Order {
    
    public Customer customer;
    public @AllowedFor(age="this.customer.age") Product product;

    @JMLClause(values={
        "assignable \nothing",
        "ensures this.customer == customer && this.product == product"})
    // :: error: inconsistent.constructor.type
    public Order(Customer customer, @AllowedFor(age="customer.age") Product product) {
        this.customer = customer;
        // :: error: assignment.type.incompatible
        this.product = product;
    }

    @JMLClause(values={"assignable \nothing"})
    public Customer getCustomer() {
        return customer;
    }

    @JMLClause(values={"assignable \nothing"})
    public @AllowedFor(age="this.customer.age") Product getProduct() {
        // :: error: return.type.incompatible
        return product;
    }
}
