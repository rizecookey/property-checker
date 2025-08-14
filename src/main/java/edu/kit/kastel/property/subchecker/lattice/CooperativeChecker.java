package edu.kit.kastel.property.subchecker.lattice;

import edu.kit.kastel.property.lattice.Lattice;

import java.net.URLClassLoader;

public interface CooperativeChecker {

    int getIdent();
    URLClassLoader getProjectClassLoader();
    int getErrorCount();
    void setErrorCount(int errorCount);
    CooperativeAnnotatedTypeFactory getTypeFactory();
    Lattice getLattice();
    CooperativeVisitor getVisitor();

    default CooperativeVisitor.Result getResult() {
        return getVisitor().getResult();
    }
}
