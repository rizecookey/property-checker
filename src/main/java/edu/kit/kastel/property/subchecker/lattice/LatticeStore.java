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

import com.sun.source.tree.Tree;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.LocalVariableNode;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.framework.util.StringToJavaExpression;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.VariableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Stream;

public final class LatticeStore extends PackingClientStore<LatticeValue, LatticeStore> {

	public LatticeStore(CFAbstractAnalysis<LatticeValue, LatticeStore, ?> analysis, boolean sequentialSemantics) {
		super(analysis, sequentialSemantics);
	}

	public LatticeStore(LatticeStore other) {
		super(other);
	}

	@Override
	protected void removeConflicting(ArrayAccess arrayAccess, @Nullable LatticeValue val) {
		clearDependents(arrayAccess.getArray());
	}

	@Override
	protected void removeConflicting(FieldAccess fieldAccess, @Nullable LatticeValue val) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();

		clearDependents(fieldAccess);

		if (thisValue != null && thisValue.toPropertyAnnotation().getAnnotationType().isNonNull()) {
			thisValue = createTopValue(thisValue.getUnderlyingType());
		}
	}

	@Override
	protected void removeConflicting(LocalVariable var) {
        clearDependents(var);
	}

	private void clearDependents(JavaExpression dependency) {
		Predicate<JavaExpression> maybeDependent;
		if (dependency instanceof FieldAccess fieldAccess) {
			var exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory()
					.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
			Tree currentTree = analysis.getCurrentTree();
			// dependency on fields may be expressed through aliases of the field owner object.
			// the util method takes this into account when searching for dependencies.
			maybeDependent = expr -> JavaExpressionUtil.maybeDependent(expr, fieldAccess, currentTree, exclFactory);
		} else {
			// if it's not a field access, it's a local variable, and dependencies on local variables cannot
			// exist through a layer of aliases.
			maybeDependent = expr -> expr.containsSyntacticEqualJavaExpression(dependency);
		}

		// this predicate is an _approximation_ for "does a given type depend on `dependency`"?
		// - if the property's arguments are all literals, it cannot depend on anything else
		// - otherwise, if the parsed concrete refinement is available
		//   (which may not be the case if unsupported language features are part of it, such as constructor calls)
		//   the type is dependent if the maybeDependent predicate defined above holds.
		Predicate<LatticeValue> isDependent =
				val -> !val.onlyLiterals() && (val.getRefinement() == null || maybeDependent.test(val.getRefinement()));

		// TODO: why do we set local variables to top type, but remove field values?
		localVariableValues.entrySet().stream()
				.filter(entry -> isDependent.test(entry.getValue()))
				.forEach(entry -> entry.setValue(createTopValue(entry.getKey().getElement().asType())));
		fieldValues.values().removeIf(isDependent);
		Optional.ofNullable(thisValue).filter(isDependent).ifPresent(val -> thisValue = null);
	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}

	/**
	 * Returns the collection of "local refinements" that are currently in this store.
	 * They include
	 * - local variable refinements
	 * - parameter refinements
	 * - refinement for the receiver ("this")
	 *
	 * The collection only contains the refinements that can be parsed as JavaExpressions.
	 *
	 * @return collection of boolean java expressions.
	 */
	public Collection<JavaExpression> getLocalRefinements() {
		// all local variable values should have the refinement set
		return Stream.concat(localVariableValues.values().stream()
				.map(LatticeValue::getRefinement), Stream.of(thisValue == null ? null : thisValue.getRefinement()))
				.filter(Objects::nonNull)
				.toList();
	}

	@Override
	public void updateForMethodCall(
			MethodInvocationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val) {

		if (atypeFactory.isSideEffectFree(node.getTarget().getMethod())) {
			return;
		}

		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		PackingStore packingStoreAfter = packingFactory.getStoreAfter(node);
		ExecutableElement method = node.getTarget().getMethod();
		AnnotatedTypeMirror.AnnotatedExecutableType exclType = exclFactory.getAnnotatedType(method);
		AnnotatedTypeMirror.AnnotatedExecutableType packingType = packingFactory.getAnnotatedType(method);
		Node receiver = node.getTarget().getReceiver();

		if (!ElementUtils.isStatic(method)) {
			// TODO: before, we passed the local receiver packing type, not the declared one. is this important? why?
			updateForPassedReference(atypeFactory, receiver,
					exclType.getReceiverType(), packingType.getReceiverType(),
					packingStoreAfter);
		}

		for (int i = 0; i < node.getArguments().size(); ++i) {
			Node arg = node.getArgument(i);
			AnnotatedTypeMirror declaredExclType = exclType.getParameterTypes().get(i);
			AnnotatedTypeMirror inputPackingType = packingType.getParameterTypes().get(i);
			if (declaredExclType.getUnderlyingType().getKind().isPrimitive()) {
				continue;
			}
			updateForPassedReference(atypeFactory, arg,
					declaredExclType, inputPackingType,
					packingStoreAfter);
		}
	}

	private void updateForPassedReference(
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			Node reference,
			AnnotatedTypeMirror declaredExclType,
			AnnotatedTypeMirror inputPackingType,
			PackingStore storeAfter
	) {
		TypeMirror underlyingType = declaredExclType.getUnderlyingType();
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);

		// Clear field values if they were possibly changed
		QualifierHierarchy exclHierarchy = exclFactory.getQualifierHierarchy();
		AnnotationMirror exclAnno = declaredExclType.getAnnotationInHierarchy(exclFactory.READ_ONLY);
		if (!exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)) {
			return;
		}

		JavaExpression owner = JavaExpression.fromNode(reference);
		CFValue outputPackingValue = storeAfter.getValue(owner);
		AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(underlyingType,
				packingFactory, false);
		if (outputPackingValue != null) {
			outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
		}

		List<VariableElement> fields = ElementUtils.getAllFieldsIn(
				TypesUtils.getTypeElement(underlyingType), atypeFactory.getElementUtils());
		for (VariableElement field : fields) {
			TypeMirror fieldOwnerType = field.getEnclosingElement().asType();

			// Don't clear fields in frame of UnknownInit input type // TODO: why not? (because packed state is unknown?)
//			if (inputPackingType.hasAnnotation(UnknownInitialization.class) &&
//					packingFactory.isInitializedForFrame(inputPackingType, fieldOwnerType)) {
//				continue;
//			}

			if (ElementUtils.isFinal(field) && ElementUtils.getType(field).getKind().isPrimitive()) {
				// final primitive fields cannot be reassigned, and they also have no fields that can be reassigned
				// so whatever their type and dependents' types were before, they stay the same.
				continue;
			}

            FieldAccess fieldAccess = new FieldAccess(owner, field);
			clearValue(fieldAccess);
			if (exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.UNIQUE)
					|| (exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)
					&& packingFactory.isInitializedForFrame(inputPackingType, fieldOwnerType))) {
				// two options to get here:
				// a) field is behind a unique reference -> can be changed
				// b) field is below packing frame of a maybe aliased reference -> can be changed
				clearDependents(fieldAccess);
			}


			// add declared type of field to store if
			// - field is part of `this` (we currently only track such fields)
			// - `this` has packed state after method
			// - field is committed after method
			if (reference instanceof ThisNode
					&& outputPackingValue != null
					&& packingFactory.isInitializedForFrame(outputPackingType, fieldOwnerType)) {
				AnnotatedTypeMirror adaptedType = atypeFactory.getAnnotatedType(field);
				LatticeValue val = analysis.createAbstractValue(adaptedType);
				val.computeRefinement(fieldAccess.toString(),
						ref -> StringToJavaExpression.atFieldDecl(ref, field, atypeFactory.getChecker()));
				insertValue(fieldAccess, val);
            }
		}
	}

	@Override
	public void initializeMethodParameter(LocalVariableNode p, @Nullable LatticeValue value) {
		if (value != null) {
			var factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
			var localPath = analysis.getTypeFactory().getPath(p.getTree());
			value.computeRefinement(p.getName(),
					ref -> StringToJavaExpression.atPath(ref, localPath, factory.getChecker()));
		}
		super.initializeMethodParameter(p, value);
	}
}
