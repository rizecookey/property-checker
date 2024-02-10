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
package tests.oopsla2021;

import java.io.File;
import java.util.List;

import org.junit.Ignore;
import org.junit.runners.Parameterized.Parameters;
import tests.property.PropertyCheckerTest;

@Ignore
@SuppressWarnings("nls")
public class CaseStudyTest extends PropertyCheckerTest {
    public CaseStudyTest(List<File> testFiles) {
        super(
                testFiles,
                "tests/oopsla2021/_case_study/lattice_nullness"
                		+ ",tests/oopsla2021/_case_study/lattice_allowedfor"
                        + ",tests/oopsla2021/_case_study/lattice_interval"
                        + ",tests/oopsla2021/_case_study/lattice_length"
                        + ",tests/oopsla2021/_case_study/lattice_okasaki"
                        + ",tests/oopsla2021/_case_study/lattice_sign",
                "tests/oopsla2021/_case_study/",
                "edu.kit.kastel.property.subchecker.lattice.case_study_qual");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"oopsla2021/_case_study"};
    }
}
