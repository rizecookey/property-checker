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

import com.sun.source.tree.ExpressionTree;
import com.sun.source.tree.MethodTree;
import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.ClassNameNode;
import org.checkerframework.dataflow.cfg.node.MethodAccessNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.AnnotationBuilder;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;

import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeKind;
import javax.lang.model.type.TypeMirror;

public final class LatticeTransfer extends PackingClientTransfer<LatticeValue, LatticeStore, LatticeTransfer> {

    private final LatticeAnnotatedTypeFactory factory;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        this.factory = analysis.getTypeFactory();
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(MethodInvocationNode node, TransferInput<LatticeValue, LatticeStore> in) {
        TypeMirror receiverType;
        LatticeStore store = in.getRegularStore();
        MethodAccessNode target = node.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        receiverType = method.getReceiverType();

        if (receiver instanceof ClassNameNode && ((ClassNameNode) receiver).getElement().toString().equals(Packing.class.getName())) {
            // Packing statements don't change the store
            return new RegularTransferResult<>(null, store, false);
        }

        if (!ElementUtils.isStatic(TreeUtils.elementFromUse(node.getTree()))
                && !node.getTarget().getMethod().getSimpleName().contentEquals("<init>")) {
            if (receiverType == null || receiverType.getKind().equals(TypeKind.NONE)) {
                //TODO in LatticeStore::updateForMethodCall. See also TMethodInvocation
                System.err.printf("warning: ignoring call to method without explicit 'this' parameter declaration: %s\n", node.getTarget());
                return new RegularTransferResult<>(null, store, true);
            }
        }

        return super.visitMethodInvocation(node, in);
    }

    @Override
    protected void processPostconditions(Node invocationNode, LatticeStore store, ExecutableElement executableElement, ExpressionTree invocationTree) {
        super.processPostconditions(invocationNode, store, executableElement, invocationTree);
    }

    @Override
    protected boolean uncommitPrimitiveFields() {
        return true;
    }

    @Override
    protected LatticeValue initialThisValue(MethodTree methodDeclTree) {
        if (!TreeUtils.isConstructor(methodDeclTree)) {
            AnnotatedTypeMirror thisType = factory.getAnnotatedType(methodDeclTree.getReceiverParameter());
            return analysis.createSingleAnnotationValue(
                    thisType.getAnnotationInHierarchy(factory.getTop()),
                    thisType.getUnderlyingType());
        } else {
            AnnotatedTypeMirror thisType = factory.getSelfType(methodDeclTree.getBody());
            return analysis.createSingleAnnotationValue(
                    factory.getTop(),
                    thisType.getUnderlyingType());
        }
    }
}
