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

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

import com.sun.source.tree.MethodTree;
import edu.kit.kastel.property.packing.PackingAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingChecker;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.packing.PackingTransfer;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.common.basetype.BaseTypeChecker;
import org.checkerframework.dataflow.cfg.visualize.CFGVisualizer;
import org.checkerframework.framework.flow.CFValue;

import javax.lang.model.element.AnnotationMirror;

public final class PropertyAnnotatedTypeFactory extends PackingAnnotatedTypeFactory {

    public PropertyAnnotatedTypeFactory(BaseTypeChecker checker) {
        super(checker);
        postInit();
    }

    @SuppressWarnings("nls")
    @Override
    protected @Nullable CFGVisualizer<CFValue, PackingStore, PackingTransfer> createCFGVisualizer() {
        if (checker.hasOption("flowdotdir")) {
            try {
                Files.createDirectories(Path.of(checker.getOption("flowdotdir")));
            } catch (IOException e) { }
        }
        return super.createCFGVisualizer();
    }

    @Override
    public PropertyChecker getChecker() {
        return (PropertyChecker) super.getChecker();
    }

    public List<AnnotationMirror> getInputPackingTypes(MethodTree tree) {
        return Collections.unmodifiableList(Arrays.asList(getChecker().getVisitor().inputPackingTypes.get(tree)));
    }

    public List<AnnotationMirror> getOutputPackingTypes(MethodTree tree) {
        return Collections.unmodifiableList(Arrays.asList(getChecker().getVisitor().outputPackingTypes.get(tree)));
    }
}
