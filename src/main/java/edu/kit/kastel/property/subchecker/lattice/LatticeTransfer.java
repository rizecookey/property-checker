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

import com.sun.source.tree.MethodTree;
import edu.kit.kastel.property.packing.PackingClientTransfer;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import edu.kit.kastel.property.util.Packing;
import org.checkerframework.dataflow.analysis.RegularTransferResult;
import org.checkerframework.dataflow.analysis.TransferInput;
import org.checkerframework.dataflow.analysis.TransferResult;
import org.checkerframework.dataflow.cfg.node.*;
import org.checkerframework.dataflow.expression.MethodCall;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.util.JavaExpressionParseUtil;
import org.checkerframework.javacutil.*;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ElementKind;
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
    public TransferResult<LatticeValue, LatticeStore> visitAssignment(AssignmentNode n, TransferInput<LatticeValue, LatticeStore> in) {
        ((LatticeAnalysis) analysis).setPosition(n.getTree());
        if (n.isSynthetic() || !(n.getTarget() instanceof LocalVariableNode local)) {
            return super.visitAssignment(n, in);
        }
        var store = in.getRegularStore();
        // when a local variable is assigned to, we store its declared type, unless the right
        // hand side of the assignment evaluates to a more specific type.
        AnnotatedTypeMirror declaredType = factory.getAnnotatedType(local.getElement());
        LatticeValue inferredValue = in.getValueOfSubNode(n.getExpression());

        AnnotatedTypeMirror inferredType = AnnotatedTypeMirror.createType(declaredType.getUnderlyingType(), factory, false);
        if (inferredValue != null) {
            inferredType.addAnnotations(inferredValue.getAnnotations());
        }
        var newVal = inferredValue != null && factory.getTypeHierarchy().isSubtype(inferredType, declaredType)
                ? inferredValue
                : analysis.createAbstractValue(declaredType);

        // this stores the type and invalidates all dependent types
        this.processCommonAssignment(in, n.getTarget(), n.getExpression(), store, newVal);
        return new RegularTransferResult<>(this.finishValue(newVal, store), store);
    }

    @Override
    public TransferResult<LatticeValue, LatticeStore> visitMethodInvocation(MethodInvocationNode node, TransferInput<LatticeValue, LatticeStore> in) {
        ((LatticeAnalysis) analysis).setPosition(node.getTree());
        TypeMirror receiverType;
        LatticeStore store = in.getRegularStore();
        MethodAccessNode target = node.getTarget();
        ExecutableElement method = target.getMethod();
        Node receiver = target.getReceiver();
        receiverType = method.getReceiverType();

        var packingClass = ElementUtils.getTypeElement(factory.getProcessingEnv(), Packing.class);
        if (receiver instanceof ClassNameNode name && name.getElement() == packingClass) {
            var packMethod = TreeUtils.getMethod(Packing.class, "pack", 2, analysis.getEnv());
            boolean isPackingCall = packMethod == method;
            if (isPackingCall) {
                // restore declared types up to specified frame after call to Packing.pack
                var packingReceiverType = node.getArgument(0).getType();
                var factory = getAnalysis().getTypeFactory();
                PackingFieldAccessAnnotatedTypeFactory packingFactory =
                        factory.getChecker().getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
                TypeMirror frame = ((FieldAccessNode) node.getArgument(1)).getReceiver().getType();
                AnnotationMirror initializedToFrameAnno = packingFactory.createUnderInitializationAnnotation(frame);
                AnnotatedTypeMirror packingType = AnnotatedTypeMirror.createType(packingReceiverType, packingFactory, false);
                packingType.addAnnotation(initializedToFrameAnno);
                insertFieldsUpToFrame(
                        store,
                        AnnotatedTypeMirror.createType(packingReceiverType, factory, false),
                        packingType,
                        false
                );
            }
            return new RegularTransferResult<>(null, store, isPackingCall);
        }

        if (!ElementUtils.isStatic(TreeUtils.elementFromUse(node.getTree()))
                && node.getTarget().getMethod().getKind() != ElementKind.CONSTRUCTOR) {
            if (receiverType == null || receiverType.getKind().equals(TypeKind.NONE)) {
                //TODO in LatticeStore::updateForMethodCall. See also TMethodInvocation
                System.err.printf("warning: ignoring call to method without explicit 'this' parameter declaration: %s\n", node.getTarget());
                // FIXME: we can't just "ignore" calls like this, since they might still result in changes
                return new RegularTransferResult<>(null, store, true);
            }
        }

        return super.visitMethodInvocation(node, in);
    }

    @Override
    public LatticeValue moreSpecificValue(LatticeValue value1, LatticeValue value2) {
        return super.moreSpecificValue(value1, value2);
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

    @Override
    protected LatticeValue createPostconditionValue(
            AnnotationMirror annotation,
            TypeMirror subjectType,
            String subject,
            MethodCall invocation
    ) {
        if (factory.declarationFromElement(invocation.getElement()) == null) {
            // method source not available
            return null;
        }
        var builder = new AnnotationBuilder(analysis.getEnv(), annotation);
        // viewpoint-adapt each field of the annotation to the invocation site
        annotation.getElementValues().forEach((element, val) -> {
            if (val.getValue() instanceof String expr) {
                String newValue;
                try {
                    newValue = JavaExpressionUtil.parseAtCallsite(expr, invocation, factory.getChecker()).toString();
                } catch (JavaExpressionParseUtil.JavaExpressionParseException e) {
                    // expression can't be parsed; new value should be something that will also
                    // prevent parsing of final refinement for consistency
                    newValue = "< " + e.getMessage() + " >";
                }
                builder.setValue(element.getSimpleName(), newValue);
            }
        });
        return analysis.createSingleAnnotationValue(builder.build(), subjectType);
    }
}
