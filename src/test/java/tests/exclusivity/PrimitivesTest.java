package tests.exclusivity;

import edu.kit.kastel.property.checker.PropertyChecker;
import org.checkerframework.framework.test.CheckerFrameworkPerDirectoryTest;
import org.junit.runners.Parameterized.Parameters;

import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import tests.property.PropertyCheckerTest;

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
public class PrimitivesTest extends PropertyCheckerTest {

    public PrimitivesTest(List<File> testFiles) {
        super(
                testFiles,
                "tests/exclusivity/lattice_nullness",
                "tests/exclusivity/primitives");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"exclusivity/primitives"};
    }
}
