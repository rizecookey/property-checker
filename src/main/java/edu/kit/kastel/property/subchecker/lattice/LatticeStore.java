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

import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import org.checkerframework.checker.initialization.qual.UnknownInitialization;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.FieldAccess;
import org.checkerframework.dataflow.expression.LocalVariable;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.type.TypeMirror;
import java.util.HashSet;
import java.util.Map;
import java.util.Set;

public final class LatticeStore extends PackingClientStore<LatticeValue, LatticeStore> {

	public LatticeStore(CFAbstractAnalysis<LatticeValue, LatticeStore, ?> analysis, boolean sequentialSemantics) {
		super(analysis, sequentialSemantics);
	}

	public LatticeStore(LatticeStore other) {
		super(other);
	}

	@Override
	protected void removeConflicting(FieldAccess fieldAccess, @Nullable LatticeValue val) {
		super.removeConflicting(fieldAccess, val);
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		// Remove all dependent qualifiers in store.
		// TODO:
		// It would be better to remove exactly those values whose dependent type depends on `fieldAccess`.

		Set<FieldAccess> fieldsToClear = new HashSet<>();
		for (Map.Entry<FieldAccess, LatticeValue> entry : fieldValues.entrySet()) {
			FieldAccess otherFieldAccess = entry.getKey();
			LatticeValue otherVal = entry.getValue();

			if (factory.getLattice().getEvaluatedPropertyAnnotation(otherVal.getAnnotations().first()) == null) {
				fieldsToClear.add(otherFieldAccess);
			}
		}
		fieldsToClear.forEach(this::clearValue);

		Set<LocalVariable> localVarsToClear = new HashSet<>();
		for (Map.Entry<LocalVariable, LatticeValue> entry : localVariableValues.entrySet()) {
			LocalVariable localVar = entry.getKey();
			LatticeValue localVal = entry.getValue();

			if (factory.getLattice().getEvaluatedPropertyAnnotation(localVal.getAnnotations().first()) == null) {
				localVarsToClear.add(localVar);
			}
		}
		localVarsToClear.forEach(v -> replaceValue(v, createTopValue(v.getElement().asType())));

		if (thisValue != null && !factory.getLattice().getPropertyAnnotation(thisValue.getAnnotations().first()).getAnnotationType().isNonNull()) {
			thisValue = createTopValue(thisValue.getUnderlyingType());
		}
	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}

	@Override
	public void updateForMethodCall(
			MethodInvocationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val) {
		Node receiver = node.getTarget().getReceiver();
		TypeMirror receiverType = node.getTarget().getMethod().getReceiverType();
		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		AnnotationMirror receiverExclAnno = receiverType == null ? null : exclFactory.getExclusivityAnnotation(
				receiverType.getAnnotationMirrors());

		// Clear field values if they were possibly changed
		boolean thisPassedAsArgument = receiverExclAnno != null &&
				receiver instanceof ThisNode &&
				exclFactory.getQualifierHierarchy().isSubtypeQualifiersOnly(receiverExclAnno, exclFactory.MAYBE_ALIASED);
		for (int i = 0; i < node.getArguments().size(); ++i) {
			Node arg = node.getArgument(i);
			AnnotationMirror argAnno = exclFactory.getExclusivityAnnotation(
					node.getTarget().getMethod().getParameters().get(i).asType().getAnnotationMirrors());
			if (arg instanceof ThisNode && exclFactory.getQualifierHierarchy()
					.isSubtypeQualifiersOnly(argAnno, exclFactory.MAYBE_ALIASED)) {
				thisPassedAsArgument = true;
				break;
			}
		}

		if (!atypeFactory.isSideEffectFree(node.getTarget().getMethod())
				&& thisPassedAsArgument) {
			PackingFieldAccessAnnotatedTypeFactory packingFactory =
					atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

			CFValue receiverOutputPackingValue = packingFactory.getStoreAfter(node).getValue((ThisNode) null);
			AnnotatedTypeMirror receiverOutputPackingType = AnnotatedTypeMirror.createType(receiverType, packingFactory, false);
			if (receiverOutputPackingValue != null) {
				receiverOutputPackingType.addAnnotations(receiverOutputPackingValue.getAnnotations());
			}

			AnnotatedTypeMirror receiverInputPackingType = packingFactory.getReceiverType(node.getTree());

			for (FieldAccess field : Set.copyOf(getFieldValues().keySet())) {
				TypeMirror fieldOwnerType = field.getField().getEnclosingElement().asType();

				// Don't clear fields in frame of UnknownInit input type
				if (receiverInputPackingType.hasAnnotation(UnknownInitialization.class) &&
						packingFactory.isInitializedForFrame(receiverInputPackingType, fieldOwnerType)) {
					continue;
				}

				// For remaining fields in frame of output type, add declared type to store
				if (receiverOutputPackingValue != null &&
						packingFactory.isInitializedForFrame(receiverOutputPackingType, fieldOwnerType)) {
					AnnotatedTypeMirror adaptedType = atypeFactory.getAnnotatedType(field.getField());
					replaceValue(
							field,
							new LatticeValue(analysis,
									adaptedType.getAnnotations(),
									adaptedType.getUnderlyingType()));
					continue;
				}

				// For remaining params, clear value
				clearValue(field);
				//System.out.printf("Clearing refinement for %s after %s\n", field, node);
			}
		}
	}
}
