package edu.kit.kastel.property.packing;

import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.initialization.InitializationFieldAccessSubchecker;
import org.checkerframework.framework.source.SourceChecker;

public class PackingFieldAccessSubchecker extends InitializationFieldAccessSubchecker {

    public PackingChecker getPackingChecker() {
        SourceChecker checker = getParentChecker();
        while (!(checker instanceof PackingChecker)) {
            checker = checker.getParentChecker();
        }
        return (PackingChecker) checker;
    }
}
