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
package edu.kit.iti.checker.property.subchecker.lattice;

import java.io.File;
import java.net.URLClassLoader;
import java.util.Collections;
import java.util.List;
import java.util.Objects;

import org.checkerframework.checker.compilermsgs.qual.CompilerMessageKey;
import org.checkerframework.common.basetype.BaseTypeChecker;
import edu.kit.iti.checker.property.checker.PropertyChecker;

public class LatticeSubchecker extends BaseTypeChecker {

    private int errorCount = 0;

    private PropertyChecker parent;
    private File latticeFile;
    private File inputDir;
    private String qualPackage;
    private int ident;
    private boolean collectingSubcheckers = false;

    public LatticeSubchecker(PropertyChecker parent, File latticeFile, File inputDir, String qualPackage, int ident) {
        this.parent = parent;
        this.latticeFile = latticeFile;
        this.inputDir = inputDir;
        this.qualPackage = qualPackage;
        this.ident = ident;
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

    @Override
    public void reportError(Object source, @CompilerMessageKey String messageKey, Object... args) {
        ++errorCount;
        super.reportError(source, messageKey, args);
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        return collectingSubcheckers ? Collections.emptyList() : super.getSubcheckers();
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

    public int getIdent() {
        return ident;
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
