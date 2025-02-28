package tests.property;

import org.junit.runners.Parameterized.Parameters;

import java.io.File;
import java.util.List;

public class MonotonicityTest extends PropertyCheckerTest {
    public MonotonicityTest(List<File> testFiles) {
        super(
                testFiles,
                "",
                "tests/property/MonotonicityTest/");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"property/MonotonicityTest"};
    }
}
