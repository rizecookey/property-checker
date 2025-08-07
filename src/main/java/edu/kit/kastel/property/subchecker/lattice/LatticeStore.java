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

import com.google.common.collect.Streams;
import com.sun.source.tree.Tree;
import com.sun.source.tree.VariableTree;
import edu.kit.kastel.property.packing.PackingClientStore;
import edu.kit.kastel.property.packing.PackingFieldAccessAnnotatedTypeFactory;
import edu.kit.kastel.property.packing.PackingFieldAccessSubchecker;
import edu.kit.kastel.property.packing.PackingStore;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.exclusivity.ExclusivityChecker;
import edu.kit.kastel.property.util.JavaExpressionUtil;
import org.apache.commons.lang3.tuple.Pair;
import org.checkerframework.checker.nullness.qual.Nullable;
import org.checkerframework.dataflow.cfg.node.MethodInvocationNode;
import org.checkerframework.dataflow.cfg.node.Node;
import org.checkerframework.dataflow.cfg.node.ObjectCreationNode;
import org.checkerframework.dataflow.cfg.node.ThisNode;
import org.checkerframework.dataflow.expression.*;
import org.checkerframework.framework.flow.CFAbstractAnalysis;
import org.checkerframework.framework.flow.CFValue;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.GenericAnnotatedTypeFactory;
import org.checkerframework.framework.type.QualifierHierarchy;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.type.TypeMirror;
import java.util.*;
import java.util.function.Predicate;
import java.util.function.ToDoubleBiFunction;
import java.util.stream.Stream;

public final class LatticeStore extends PackingClientStore<LatticeValue, LatticeStore> {

	private final TypeMirror stringType = ElementUtils.getTypeElement(analysis.getEnv(), String.class).asType();

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
        clearDependents(fieldAccess);
	}

	@Override
	protected void removeConflicting(LocalVariable var) {
        clearDependents(var);
	}

	// TODO investigate performance issue in code below

	private void clearDependents(JavaExpression dependency) {
		Predicate<JavaExpression> exprAnalyzer;
		Tree currentTree = ((LatticeAnalysis) analysis).getLocalTree();
		if (currentTree instanceof VariableTree) {
			// we are in a variable declaration/assignment. No type can depend on an undeclared variable,
			// so there are no dependents up to this point.
			return;
		}

		if (dependency instanceof FieldAccess fieldAccess) {
			var exclFactory = (ExclusivityAnnotatedTypeFactory) analysis.getTypeFactory()
					.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
			// dependency on fields may be expressed through aliases of the field owner object.
			// the util method takes this into account when searching for dependencies.
			exprAnalyzer = expr -> JavaExpressionUtil.maybeDependent(expr, fieldAccess, currentTree, exclFactory);
		} else {
			// if it's not a field access, it's a local variable, and dependencies on local variables cannot
			// exist through a layer of aliases.
			exprAnalyzer = expr -> expr.containsSyntacticEqualJavaExpression(dependency);
		}

		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		// this predicate is a conservative _approximation_ for "does a given type depend on `dependency`"?
		// it will always return true if the refinement information is missing.
		Predicate<Map.Entry<? extends JavaExpression, LatticeValue>> isDependent =
				entry -> !entry.getKey().equals(dependency) // dependents don't include the value itself
						&& factory.getLattice().getEvaluatedPropertyAnnotation(entry.getValue().getAnnotations().first()) == null
						&& entry.getValue().getRefinementParams(entry.getKey()).parallel().map(exprAnalyzer::test).anyMatch(Boolean::booleanValue);

		// We set local variable types to top if they're invalidated. If we removed them from the store,
		// the framework would incorrectly fall back to their declared type
		localVariableValues.entrySet().stream()
				.filter(isDependent)
				.forEach(entry -> entry.setValue(createTopValue(entry.getKey().getElement().asType())));
		fieldValues.entrySet().removeIf(isDependent);
		methodValues.entrySet().removeIf(isDependent);
		Optional.ofNullable(thisValue)
				// special case for non null annotations on `this` - they can never be invalidated
				.filter(val -> !val.getPropertyAnnotation().getAnnotationType().isNonNull())
				.filter(val -> isDependent.test(Map.entry(new ThisReference(val.getUnderlyingType()), val)))
				.ifPresent(val -> thisValue = createTopValue(val.getUnderlyingType()));


	}

	protected LatticeValue createTopValue(TypeMirror underlyingType) {
		LatticeAnnotatedTypeFactory factory = (LatticeAnnotatedTypeFactory) analysis.getTypeFactory();
		return analysis.createSingleAnnotationValue(factory.getTop(), underlyingType);
	}


	/**
	 * Returns a stream of all the refinements that are currently in this store (the "local refinement context).
	 * They include
	 * <ul>
	 *     <li>local variable refinements</li>
	 *     <li>parameter refinements</li>
	 *     <li>field refinements</li>
	 *     <li>method return value refinements</li>
	 *     <li>refinement for the receiver ("this")</li>
	 * </ul>
	 *
	 * The collection only contains the refinements that can be parsed as JavaExpressions.
	 *
	 * @return collection of boolean java expressions.
	 */
	public Stream<JavaExpression> allRefinements() {
		return Streams.concat(
				fieldValues.entrySet().stream(),
				localVariableValues.entrySet().stream(),
				methodValues.entrySet().stream(),
				getThisValue().map(val -> Map.entry(new ThisReference(val.getUnderlyingType()), val)).stream()
		).flatMap(entry -> entry.getValue().getRefinement(entry.getKey()).stream());
	}

	public Optional<LatticeValue> getThisValue() {
		return Optional.ofNullable(thisValue);
	}

	@Override
	public void updateForMethodCall(
			MethodInvocationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		updateForInvocation((MethodCall) JavaExpression.fromNode(node), node, atypeFactory, val);
	}

	/**
	 * Same as {@link #updateForMethodCall(MethodInvocationNode, GenericAnnotatedTypeFactory, LatticeValue)},
	 * but for constructor ("new") calls. The rules for type invalidation are the same for constructors as they are
	 * for methods (we look for fields in references passed arguments that could have been changed).
	 *
	 * @param node ObjectCreationNode
	 * @param atypeFactory type factory
	 * @param val inferred return value of the constructor call
	 */
	public void updateForObjectCreation(
			ObjectCreationNode node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		updateForInvocation(JavaExpressionUtil.constructorCall(node.getTree()), node, atypeFactory, val);
	}

	private void updateForInvocation(
			MethodCall invocation,
			Node node, // either a ObjectCreationNode or MethodInvocationNode
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			LatticeValue val
	) {
		ExecutableElement method = invocation.getElement();
		if (atypeFactory.isSideEffectFree(method) && atypeFactory.isDeterministic(method)) {
			// insert return value into store if method is pure and not a constructor call (like this(...) or super(...))
			if (method.getKind() != ElementKind.CONSTRUCTOR || invocation.getReceiver() instanceof ClassName) {
				insertValue(invocation, val);
			}
			return;
		}

		for (var fieldAccess : changedFields(invocation, node, atypeFactory)) {
			clearValue(fieldAccess);
			clearDependents(fieldAccess);
		}

		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		PackingStore packingStoreAfter = packingFactory.getStoreAfter(node);

		updateCommittedFields(invocation, packingStoreAfter, packingFactory);
	}

	public List<FieldAccess> changedFields(
			MethodCall invocation,
			Node node,
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory
	) {
		ExecutableElement method = invocation.getElement();

		if (atypeFactory.isSideEffectFree(method)) {
			// no field can be modified if method is side effect free
			return List.of();
		}

		List<FieldAccess> result = new ArrayList<>();

		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);

        AnnotatedTypeMirror.AnnotatedExecutableType exclType = exclFactory.getAnnotatedType(method);
		AnnotatedTypeMirror.AnnotatedExecutableType packingType = packingFactory.getAnnotatedType(method);

		if (!ElementUtils.isStatic(method) && method.getKind() != ElementKind.CONSTRUCTOR) {
			Node receiver = ((MethodInvocationNode) node).getTarget().getReceiver();
			// receivers of instance method calls could be modified by the method
            var packingReceiver = packingType.getReceiverType();
			var exclReceiver = exclType.getReceiverType();
			// TODO: can a method without an explicit receiver parameter change the receiver's fields?
			//  if so, we must still call updateForPassedReference here with the default exclusivity and packing types
			if (packingReceiver != null) {
				result.addAll(changedFields(atypeFactory, receiver, exclReceiver, packingReceiver));
			}
		}

		// go through all the passed arguments, see which ones could have been modified
		List<Node> arguments = switch (node) {
			case MethodInvocationNode mi -> mi.getArguments();
			case ObjectCreationNode oc -> oc.getArguments();
			default -> throw new AssertionError();
		};

		for (int i = 0; i < arguments.size(); ++i) {
			// arguments of method/constructor calls could be modified by the implementation
			Node arg = arguments.get(i);
            var inputPackingType = packingType.getParameterTypes().get(i);
			var inputExclType = exclType.getParameterTypes().get(i);
			result.addAll(changedFields(atypeFactory, arg, inputExclType, inputPackingType));
		}

		return result;
	}

	private List<FieldAccess> changedFields(
			GenericAnnotatedTypeFactory<LatticeValue, LatticeStore, ?, ?> atypeFactory,
			Node passedValue,
			AnnotatedTypeMirror inputExclType,
			AnnotatedTypeMirror inputPackingType
	) {
		if (passedValue instanceof ObjectCreationNode) {
			// reference is a constructor call. Changes to fields like new Foo().field
			// are irrelevant because they are not visible to the caller
			return List.of();
		}

		if (passedValue.getType().getKind().isPrimitive()
				|| analysis.getTypes().isSameType(passedValue.getType(), stringType)) {
			// skip primitive and string types - they can't be modified
			// the reason we handle strings explicitly here is that they can also be literals,
			// and this store can't deal with literal values.
			return List.of();
		}

		JavaExpression passedExpr = JavaExpression.fromNode(passedValue);

		List<FieldAccess> result = new ArrayList<>();
        PackingFieldAccessAnnotatedTypeFactory packingFactory =
				atypeFactory.getTypeFactoryOfSubcheckerOrNull(PackingFieldAccessSubchecker.class);
		ExclusivityAnnotatedTypeFactory exclFactory = atypeFactory.getTypeFactoryOfSubchecker(ExclusivityChecker.class);
		QualifierHierarchy exclHierarchy = exclFactory.getQualifierHierarchy();

		// TODO: what about static fields? any non-final static field could have changed,
		//  so anything depending on a static non-final field should be invalidated
		// (field owner, packing type of field owner)
		Deque<Pair<JavaExpression, AnnotatedTypeMirror>> contexts = new ArrayDeque<>();
		// pseudo this reference as "root" of field accesses based on passed reference
		contexts.push(Pair.of(new ThisReference(passedValue.getType()), inputPackingType));
		while (!contexts.isEmpty()) {
			var context = contexts.pop();
			var fieldOwner = context.getLeft();
			var packingType = context.getRight();

			if (fieldOwner.getType().getKind().isPrimitive()) {
				// primitive types have no fields
				continue;
			}

			var fieldOwnerType = TypesUtils.getTypeElement(fieldOwner.getType());
			if (fieldOwnerType == null) {
				// type variables have no fields
				continue;
			}

			var exclAnno = exclFactory.deriveExclusivityValue(inputExclType, fieldOwner);
			if (!exclHierarchy.isSubtypeQualifiersOnly(exclAnno, exclFactory.MAYBE_ALIASED)) {
				// context is @ReadOnly, so none of its fields could have been modified
				continue;
			}

			// compute all fields (including nested fields) that could have been modified,
			// based on the uniqueness and packing information

			var modifiedFields = ElementUtils.getAllFieldsIn(
							fieldOwnerType, atypeFactory.getElementUtils())
					.stream();

			if (AnnotationUtils.areSame(exclFactory.MAYBE_ALIASED, exclAnno)) {
				// for @MaybeAliased contexts, only the uncommitted fields could have been modified
				modifiedFields = modifiedFields.filter(field ->
						packingFactory.isInitializedForFrame(packingType, field.getEnclosingElement().asType()));
			}

			// fieldOwner starts with `this`, which must be substituted by the actual expression that was passed
			JavaExpression fullReceiver = fieldOwner.atFieldAccess(passedExpr);

			// Add acyclic fields that aren't final to result, continue with field traversal
			modifiedFields.map(field -> new FieldAccess(fullReceiver, field))
					.filter(this::acyclic)
					.forEach(fieldAccess -> {
						contexts.push(Pair.of(fieldAccess, packingFactory.getAnnotatedType(fieldAccess.getField())));
						if (!ElementUtils.isFinal(fieldAccess.getField())) {
							result.add(fieldAccess);
						}
					});
		}
		return result;
	}

	private void updateCommittedFields(
			MethodCall invocation,
			PackingStore storeAfter,
			PackingFieldAccessAnnotatedTypeFactory packingFactory
	) {
		// update the type of the fields in `this` after a method or constructor call,
		// based on the packing type of `this` after the method call
		boolean thisPassed = Stream.concat(Stream.of(invocation.getReceiver()), invocation.getArguments().stream())
				.anyMatch(val -> val instanceof ThisReference);
		if (!thisPassed) {
			return;
		}

		CFValue outputPackingValue = storeAfter.getValue((ThisNode) null);
		TypeMirror thisType = getThisValue().orElseThrow().getUnderlyingType();
		AnnotatedTypeMirror outputPackingType = AnnotatedTypeMirror.createType(thisType,
				packingFactory, false);
		if (outputPackingValue != null) {
			outputPackingType.addAnnotations(outputPackingValue.getAnnotations());
			var packingAnno = outputPackingType.getAnnotationInHierarchy(packingFactory.getUnknownInitialization());
			var frame = packingFactory.getTypeFrameFromAnnotation(packingAnno);
			var initializedFields = ElementUtils.getAllFieldsIn(TypesUtils.getTypeElement(frame), packingFactory.getElementUtils());
			for (var field : initializedFields) {
				AnnotatedTypeMirror adaptedType = analysis.getTypeFactory().getAnnotatedType(field);
				var invocationTree = ((LatticeAnalysis) analysis).getLocalTree();
				// temporarily set analysis position to field so its refinement can be parsed at its declaration
				((LatticeAnalysis) analysis).setPosition(field);
				LatticeValue val = analysis.createAbstractValue(adaptedType);
				((LatticeAnalysis) analysis).setPosition(invocationTree);
				insertValue(new FieldAccess(new ThisReference(thisType), field), val);
			}
		}
	}

	private boolean acyclic(FieldAccess expr) {
		var accessedFields = Stream.iterate(expr,
						fa -> fa.getReceiver() instanceof FieldAccess,
						fa -> (FieldAccess) fa.getReceiver()
				)
				.map(FieldAccess::getField)
				.toList();
		return accessedFields.size() == Set.copyOf(accessedFields).size();
	}
}
