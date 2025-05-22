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
package tests.daikon;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.apache.commons.lang3.ObjectUtils;
import org.checkerframework.framework.test.*;
import org.junit.Test;

import java.io.File;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

public class DaikonTest {

    /** The files containing test code, which will be type-checked. */
    protected final String testDir = "daikon";

    /** The binary names of the checkers to run. */
    protected final String lattices = "tests/daikon/lattice_nullnessnode";

    protected final List<String> classpathExtra = List.of(
            "tests/daikon/typequals",
            "tests/daikon/jtb",
            "tests/daikon/lib/bcel-6.8.1.jar",
            "tests/daikon/lib/bcel-util-1.2.1.jar",
            //"lib/checker-qual-3.42.0-eisop3-SNAPSHOT.jar",
            "tests/daikon/lib/commons-exec-1.4.0.jar",
            "tests/daikon/lib/commons-lang3-3.15.0.jar",
            "tests/daikon/lib/hamcrest-core-1.3-Daikon.jar",
            "tests/daikon/lib/hashmap-util-0.0.1.jar",
            "tests/daikon/lib/java-getopt-1.0.14.0.1.jar",
            "tests/daikon/lib/junit-4.13.2-Daikon.jar",
            "tests/daikon/lib/junit-platform-console-standalone-1.9.0-Daikon.jar",
            "tests/daikon/lib/options-1.0.6.jar",
            "tests/daikon/lib/plume-util-1.9.3.jar",
            "tests/daikon/lib/daikon-plumelib.jar",
            "tests/daikon/lib/checker-framework/checker-3.42.0-eisop3-SNAPSHOT.jar",
            "tests/daikon/lib/reflection-util-1.1.3.jar"
    );

    /** Extra options to pass to javac when running the checker. */
    protected final List<String> checkerOptions = List.of(
            "-Anomsgtext",
            "-Astubs=stubs/",
            "-nowarn",
            //"-Aflowdotdir=../flowdot",
            "-APropertyChecker_inDir=" + new File(new File("tests"), testDir).getPath(),
            "-APropertyChecker_outDir=" + "../property-checker-out",
            "-APropertyChecker_lattices=" + lattices,
            "-APropertyChecker_qualPkg=" + "edu.kit.kastel.property.subchecker.lattice.daikon_qual",
            "-APropertyChecker_noInferUnpack=true",
            "-APropertyChecker_translationOnly=" + ObjectUtils.defaultIfNull(System.getProperty("translationOnly"), "false"));

    /** Run the tests. */
    @Test
    public void run() {
        List<File> testFiles = Arrays.stream(new File(resolveTestDirectory(), testDir + "/daikon/diff").listFiles()).filter(f -> f.getName().endsWith(".java")).toList();
        boolean shouldEmitDebugInfo = TestUtilities.getShouldEmitDebugInfo();
        TestConfiguration config =
                TestConfigurationBuilder.buildDefaultConfiguration(
                        new File(resolveTestDirectory(), testDir).getPath(),
                        testFiles,
                        classpathExtra,
                        Collections.singletonList(PropertyChecker.class.getName()),
                        checkerOptions,
                        shouldEmitDebugInfo);
        TypecheckResult testResult = new TypecheckExecutor().runTest(config);
        TestUtilities.assertTestDidNotFail(testResult);
    }

    protected File resolveTestDirectory() {
        TestRootDirectory annotation = getClass().getAnnotation(TestRootDirectory.class);
        if (annotation != null) {
            return new File(annotation.value());
        }
        return new File("tests");
    }
}
