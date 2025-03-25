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

import com.sun.source.tree.LiteralTree;
import com.sun.source.tree.MethodTree;
import com.sun.source.tree.Tree;
import edu.kit.kastel.property.lattice.EvaluatedPropertyAnnotation;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.util.ClassUtils;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.ClassNameNode;
import org.checkerframework.dataflow.cfg.node.MethodAccessNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.expression.JavaExpression;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.javacutil.TreeUtils;

public final class LatticeTransfer extends PackingClientTransfer<LatticeValue, LatticeStore, LatticeTransfer> {

    private final LatticeAnnotatedTypeFactory factory;

    public LatticeTransfer(LatticeAnalysis analysis) {
        super(analysis);
        this.factory = analysis.getTypeFactory();
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(MethodInvocationNode node, TransferInput<LatticeValue, LatticeStore> in) {
        LatticeStore store = in.getRegularStore();
        MethodAccessNode target = node.getTarget();
        Node receiver = target.getReceiver();

        if (receiver instanceof ClassNameNode && ((ClassNameNode) receiver).getElement().toString().equals(Packing.class.getName())) {
            // Packing statements don't change the store
            return new RegularTransferResult<>(null, store, false);
        }

        return super.visitMethodInvocation(node, in);
    }

    @Override
    protected void processCommonAssignment(TransferInput<LatticeValue, LatticeStore> in, Node lhs, Node rhs, LatticeStore store, LatticeValue rhsValue) {
        // If the rhs is a literal that is compatible with the lhs's declared type, put that type in the store.
        boolean compatible = false;
        AnnotatedTypeMirror lhsDeclType = factory.getAnnotatedTypeLhs(lhs.getTree());
        if (rhs.getTree() instanceof LiteralTree) {
            LiteralTree literal = (LiteralTree) rhs.getTree();
            Lattice lattice = factory.getLattice();
            PropertyAnnotation pa = lattice.getPropertyAnnotation(lhsDeclType);
            EvaluatedPropertyAnnotation epa = lattice.getEvaluatedPropertyAnnotation(factory.getAnnotatedTypeLhs(lhs.getTree()));

            if (factory.getAnnotatedType(rhs.getTree()).getUnderlyingType().toString().equals("java.lang.String") && pa.getAnnotationType().isNonNull()) {
                compatible = true;
            } else if (epa != null) {
                PropertyAnnotationType pat = epa.getAnnotationType();

                if (pat.getSubjectType() != null) {
                    Class<?> literalClass = ClassUtils.literalKindToClass(literal.getKind());
                    if (literalClass != null && literalClass.equals(pat.getSubjectType())) {
                        if (epa.checkProperty(literal.getValue())) {
                            compatible = true;
                        }
                    } else if (literal.getKind() == Tree.Kind.NULL_LITERAL && !pat.getSubjectType().isPrimitive()) {
                        if (epa.checkProperty(null)) {
                            compatible = true;
                        }
                    }
                }
            }
        }

        if (compatible) {
            store.insertValue(JavaExpression.fromNode(lhs), new LatticeValue(analysis, lhsDeclType.getAnnotations(), lhsDeclType.getUnderlyingType()));
            return;
        }

        super.processCommonAssignment(in, lhs, rhs, store, rhsValue);
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
            boolean isNonNull = factory.getLattice().getPropertyAnnotation(thisType).getAnnotationType().isNonNull();
            return analysis.createSingleAnnotationValue(
                    isNonNull ? thisType.getAnnotationInHierarchy(factory.getTop()) : factory.getTop(),
                    thisType.getUnderlyingType());
        }
    }
}
