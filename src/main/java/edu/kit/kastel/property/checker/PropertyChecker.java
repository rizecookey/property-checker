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
package edu.kit.kastel.property.checker;

import java.io.File;
import java.util.*;

import edu.kit.kastel.property.packing.PackingChecker;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.framework.source.SupportedOptions;

import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.subchecker.lattice.LatticeSubchecker;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;

@SupportedOptions({
    Config.LATTICES_FILE_OPTION,
    Config.INPUT_DIR_OPTION,
    Config.OUTPUT_DIR_OPTION,
    Config.QUAL_PKG_OPTION,
    Config.TRANSLATION_JML_DIALECT_OPTION,
    Config.TRANSLATION_ONLY_OPTION,
    Config.NO_EXCLUSITIVY_OPTION,
    "assumeInitialized"
})
public final class PropertyChecker extends PackingChecker {

    private ExclusivityChecker exclusivityChecker;
    private PackingFieldAccessSubchecker fieldAccessChecker;
    private List<LatticeSubchecker> latticeSubcheckers;
    private List<BaseTypeChecker> packingTargetCheckers;

    private Map<String, PriorityQueue<LatticeVisitor.Result>> results = new HashMap<>();

    public PropertyChecker() { }

    @Override
    public boolean checkPrimitives() {
        return true;
    }

    @Override
    public List<BaseTypeChecker> getTargetCheckers() {
        if (packingTargetCheckers == null) {
            packingTargetCheckers = new ArrayList<>();
            packingTargetCheckers.add(getExclusivityChecker());
            packingTargetCheckers.addAll(getLatticeSubcheckers());
        }

        return packingTargetCheckers;
    }

    @Override
    public List<BaseTypeChecker> getSubcheckers() {
        List<BaseTypeChecker> checkers = new ArrayList<>();
        checkers.add(getFieldAccessChecker());
        checkers.add(getExclusivityChecker());
        checkers.addAll(getLatticeSubcheckers());
        return checkers;
    }

    @Override
    public <T extends BaseTypeChecker> @Nullable T getSubchecker(Class<T> checkerClass) {
        for (BaseTypeChecker checker : getSubcheckers()) {
            if (checker.getClass() == checkerClass) {
                return (T) checker;
            }
        }

        return null;
    }

    public ExclusivityChecker getExclusivityChecker() {
        if (exclusivityChecker == null) {
            exclusivityChecker = new ExclusivityChecker(this);
        }

        return exclusivityChecker;
    }

    public PackingFieldAccessSubchecker getFieldAccessChecker() {
        if (fieldAccessChecker == null) {
            fieldAccessChecker = new PackingFieldAccessSubchecker(this);
        }

        return fieldAccessChecker;
    }

    public List<LatticeSubchecker> getLatticeSubcheckers() {
        if (latticeSubcheckers == null) {
            latticeSubcheckers = new ArrayList<>();

            String[] lattices = getLattices();
            String inputDir = getInputDir();
            String qualPackage = getQualPackage();

            int ident = 0;
            for (String lattice : lattices) {
                latticeSubcheckers.add(new LatticeSubchecker(this, new File(lattice.strip()), new File(inputDir), qualPackage, ident++));
            }
        }

        return Collections.unmodifiableList(latticeSubcheckers);
    }
    
    public String[] getLattices() {
    	return getOption(Config.LATTICES_FILE_OPTION).split(Config.SPLIT);
    }

    public String getOutputDir() {
    	return getOption(Config.OUTPUT_DIR_OPTION);
    }
    
    public String getQualPackage() {
    	return getOption(Config.QUAL_PKG_OPTION);
    }

    public void addResult(String fileName, LatticeVisitor.Result result) {
        if (!results.containsKey(fileName)) {
            results.put(fileName, new PriorityQueue<>(
                        (r0, r1) -> r0.getChecker().getIdent() - r1.getChecker().getIdent()));

            results.get(fileName).add(result);
        } else {
            Optional<LatticeVisitor.Result> optional = results.get(fileName).stream().filter(r -> r.getChecker().equals(result.getChecker())).findAny();
            if (optional.isPresent()) {
                LatticeVisitor.Result r = optional.get();
                r.addAll(result);
            } else {
                results.get(fileName).add(result);
            }
        }
    }

    public List<LatticeVisitor.Result> getResults(String fileName) {
        PriorityQueue<LatticeVisitor.Result> q = results.get(fileName);
        return q != null ? Collections.unmodifiableList(new ArrayList<>(q)) : Collections.emptyList();
    }

    public PropertyAnnotatedTypeFactory getPropertyFactory() {
        return (PropertyAnnotatedTypeFactory) getTypeFactory();
    }
}
