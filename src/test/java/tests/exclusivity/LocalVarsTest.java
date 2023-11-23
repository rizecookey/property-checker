package tests.exclusivity;

import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;

import java.io.File;
import java.util.List;

/**
 * Test runner for tests of the Exclusivity Checker.
 *
 * <p>Tests appear as Java files in the {@code tests/exclusivity} folder. To add a new test case,
 * create a Java file in that directory. The file contains "// ::" comments to indicate expected
 * errors and warnings; see
 * https://github.com/typetools/checker-framework/blob/master/checker/tests/README .
 */
public class LocalVarsTest extends CheckerFrameworkPerDirectoryTest {
    public LocalVarsTest(List<File> testFiles) {
        super(
                testFiles,
                ExclusivityChecker.class,
                "exclusivity/localvars",
                "-Anomsgtext",
                "-Astubs=stubs/",
                "-Aflowdotdir=../flowdot",
                "-nowarn");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"exclusivity/localvars"};
    }
}
