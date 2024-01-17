package tests.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

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
public class InitializationTest extends CheckerFrameworkPerDirectoryTest {
    public InitializationTest(List<File> testFiles) {
        super(
                testFiles,
                PropertyChecker.class,
                "exclusivity/initialization",
                "-Anomsgtext",
                "-Astubs=stubs/",
                "-nowarn");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"exclusivity/initialization"};
    }
}
