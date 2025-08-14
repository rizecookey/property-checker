package tests.exclusivity;

import org.junit.runners.Parameterized.Parameters;
import tests.property.PropertyCheckerTest;

import java.io.File;
import java.util.List;

//TODO
// Handling of exceptions in the Packing Checker is currently unsound.
// See also related Checker Framework issues like
// https://github.com/eisop/checker-framework/issues/1181

public class ExceptionTest extends PropertyCheckerTest {
    public ExceptionTest(List<File> testFiles) {
        super(
                testFiles,
                "tests/property/lattice_simple",
                "tests/exclusivity/exception");
    }

    @Parameters
    public static String[] getTestDirs() {
        return new String[] {"exclusivity/exception"};
    }
}
