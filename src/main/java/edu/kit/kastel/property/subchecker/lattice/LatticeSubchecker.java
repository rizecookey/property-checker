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
package edu.kit.kastel.property.subchecker.lattice;

import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;

import java.io.File;
import java.net.URLClassLoader;
import java.util.List;
import java.util.Objects;

public final class LatticeSubchecker extends BaseTypeChecker implements CooperativeChecker {

    private int errorCount = 0;

    private PropertyChecker parent;
    private File latticeFile;
    private File inputDir;
    private String qualPackage;
    private int ident;

    public LatticeSubchecker(PropertyChecker parent, File latticeFile, File inputDir, String qualPackage, int ident) {
        this.parent = parent;
        this.latticeFile = latticeFile;
        this.inputDir = inputDir;
        this.qualPackage = qualPackage;
        this.ident = ident;

        setProcessingEnvironment(parent.getProcessingEnvironment());
        treePathCacher = parent.getTreePathCacher();
        setParentChecker(parent);
    }

    @Override
    public int hashCode() {
        return Objects.hash(latticeFile.getAbsolutePath(), inputDir.getAbsolutePath());
    }

    @Override
    public boolean equals(Object obj) {
        if (obj instanceof LatticeSubchecker) {
            LatticeSubchecker other = (LatticeSubchecker) obj;
            return latticeFile.getAbsolutePath().equals(other.latticeFile.getAbsolutePath())
                    && inputDir.getAbsolutePath().equals(other.inputDir.getAbsolutePath());
        } else {
            return false;
        }
    }

    @Override
    public PropertyChecker getParentChecker() {
        return parent;
    }

    public ExclusivityChecker getExclusivityChecker() {
        return parent.getExclusivityChecker();
    }

    public ExclusivityAnnotatedTypeFactory getExclusivityFactory() {
        return getExclusivityChecker().getTypeFactory();
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        return List.of(); // return List.of(parent.getExclusivityChecker());
    }

    @Override
    public <T extends BaseTypeChecker> @Nullable T getSubchecker(Class<T> checkerClass) {
        return getParentChecker().getSubchecker(checkerClass);
    }

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        ++errorCount;
        super.reportError(source, getTypeFactory().getLattice().getIdent() + "." + messageKey, args);
    }

    public File getLatticeFile() {
        return latticeFile;
    }

    public File getInputDir() {
        return inputDir;
    }

    public String getQualPackage() {
        return qualPackage;
    }

    public URLClassLoader getProjectClassLoader() {
        return parent.getProjectClassLoader();
    }

    @Override
    public int getIdent() {
        return ident;
    }

    @Override
    public Lattice getLattice() {
        return getTypeFactory().getLattice();
    }

    @Override
    public LatticeAnnotatedTypeFactory getTypeFactory() {
        return (LatticeAnnotatedTypeFactory) super.getTypeFactory();
    }

    public int getErrorCount() {
        return errorCount;
    }

    public void setErrorCount(int errorCount) {
        this.errorCount = errorCount;
    }
}
