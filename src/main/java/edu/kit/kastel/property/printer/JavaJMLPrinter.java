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
package edu.kit.kastel.property.printer;

import com.google.common.collect.Streams;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.MemberSelectTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.*;
import com.sun.tools.javac.tree.TreeInfo;
import edu.kit.kastel.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.kastel.property.checker.PropertyChecker;
import edu.kit.kastel.property.checker.qual.JMLClause;
import edu.kit.kastel.property.checker.qual.JMLClauseTranslationOnly;
import edu.kit.kastel.property.checker.qual.JMLClauses;
import edu.kit.kastel.property.checker.qual.JMLClausesTranslationOnly;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.lattice.Checkable;
import edu.kit.kastel.property.lattice.Lattice;
import edu.kit.kastel.property.lattice.PropertyAnnotation;
import edu.kit.kastel.property.lattice.PropertyAnnotationType;
import edu.kit.kastel.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.kastel.property.subchecker.lattice.LatticeVisitor;
import edu.kit.kastel.property.util.TypeUtils;
import edu.kit.kastel.property.util.Union;
import org.apache.commons.lang3.StringUtils;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;
import org.checkerframework.javacutil.TreeUtils;
import org.checkerframework.javacutil.TypesUtils;

import javax.lang.model.element.*;
import javax.lang.model.type.TypeKind;
import javax.lang.model.util.ElementFilter;
import java.io.BufferedWriter;
import java.io.IOException;
import java.util.*;
import java.util.stream.Collectors;

import static com.sun.tools.javac.code.Flags.*;
import static com.sun.tools.javac.tree.JCTree.Tag.SELECT;

@SuppressWarnings("nls")
public class JavaJMLPrinter extends PrettyPrinter {

    public static boolean TRANSLATION_RAW = false;

    public static String printCheckable(Checkable chk, PropertyAnnotation pa, String subject) {
        String cond = chk.getCondition();

        if (subject != null) {
            cond = cond.replace('§' + Config.SUBJECT_NAME + '§', subject);

            for (int i = 1; i < chk.getParameterNames().length; ++i) {
                String paramName = chk.getParameterNames()[i];
                cond = cond.replace('§' + paramName + '§', pa.getActualParameters().get(i - 1));
            }
        } else {
            for (int i = 0; i < chk.getParameterNames().length; ++i) {
                String paramName = chk.getParameterNames()[i];
                cond = cond.replace('§' + paramName + '§', pa.getActualParameters().get(i));
            }
        }

        return '(' + cond + ')';
    }

    protected List<LatticeVisitor.Result> results;
    protected PropertyAnnotatedTypeFactory propertyFactory;
    
    protected int assertions = 0;
    protected int assumptions = 0;
    protected int methodCallPreconditions = 0;
    protected int freeMethodCallPreconditions = 0;
    protected int methodCallPostconditions = 0;
    protected int freeMethodCallPostconditions = 0;

    protected int tempVarNum = 0;
    protected JCClassDecl enclClass;
    protected JCMethodDecl enclMethod;
    protected boolean enclBlock = false;

    public JavaJMLPrinter(
            List<LatticeVisitor.Result> results,
            PropertyChecker propertyChecker,
            BufferedWriter out) {
        super(out, true);
        this.results = results;
        this.propertyFactory = propertyChecker.getPropertyFactory();
        
        String translationOnlyOption = propertyChecker.getOption(Config.TRANSLATION_ONLY_OPTION);
        
        if (Objects.equals(translationOnlyOption, "true")) {
        	TRANSLATION_RAW = true;
        }
    }
    
    public int getAssertions() {
		return assertions;
	}
    
    public int getAssumptions() {
		return assumptions;
	}
    
    public int getMethodCallPreconditions() {
		return methodCallPreconditions;
	}
    
    public int getFreeMethodCallPreconditions() {
		return freeMethodCallPreconditions;
	}

    public int getMethodCallPostconditions() {
        return methodCallPostconditions;
    }

    public int getFreeMethodCallPostconditions() {
        return freeMethodCallPostconditions;
    }

    @Override
    public void visitImport(JCImport tree) {
        String str = tree.qualid.toString();
    	if (str.startsWith("edu.kit.kastel.property")
                || str.startsWith("org.checkerframework.checker.initialization")) {
    		return;
    	}
    	
    	super.visitImport(tree);
    }

    @Override
    public void visitClassDef(JCClassDecl tree) {
        try {
            println();
            align();
            printDocComment(tree);
            printFlags(tree.mods.flags & ~INTERFACE);

            JCClassDecl enclClassPrev = enclClass;
            enclClass = tree;

            if (isInterface(tree)) {
                print("interface " + tree.name);
                printTypeParameters(tree.typarams);
                if (tree.implementing.nonEmpty()) {
                    print(" extends ");
                    printExprs(tree.implementing);
                }
            } else {
                if ((tree.mods.flags & ENUM) != 0) {
                    print("enum " + tree.name);
                } else {
                    print("class " + tree.name);
                }
                printTypeParameters(tree.typarams);
                if (tree.extending != null) {
                    print(" extends ");
                    printExpr(tree.extending);
                }
                if (tree.implementing.nonEmpty()) {
                    print(" implements ");
                    printExprs(tree.implementing);
                }
            }

            print(" ");

            if ((tree.mods.flags & ENUM) != 0) {
                printEnumBody(tree.defs);
            } else {
                println(" {");
                indent();

                //TODO Add this to Object class in KeY JavaRedux
                /*println();
                printlnAligned("//@ public ghost Class packed = Object.class;");
                println();*/

                if (!isInterface(tree)) {
                    printStaticInitializers();
                }

                String containingClassName = enclClass.sym.getQualifiedName().toString();

                println();

                for (LatticeVisitor.Result wellTypedness : results) {
                    Lattice lattice = wellTypedness.getLattice();

                    List<VariableElement> allFields = ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());
                    for (VariableElement field : allFields) {
                        if (!field.asType().getKind().isPrimitive()) {
                            if (ElementUtils.isStatic(field)) {
                                printlnAligned(String.format(
                                        "//@ public static invariant_free packed <: %s ==> %s;",
                                        containingClassName,
                                        getPackedCondition(
                                                propertyFactory.getAnnotatedType(field).getAnnotationInHierarchy(propertyFactory.getInitialized()),
                                                field.getSimpleName().toString())));
                            } else {
                                printlnAligned(String.format(
                                        "//@ public invariant_free packed <: %s ==> %s;",
                                        containingClassName,
                                        getPackedCondition(
                                                propertyFactory.getAnnotatedType(field).getAnnotationInHierarchy(propertyFactory.getInitialized()),
                                                field.getSimpleName().toString())));
                            }
                        }
                    }

                    for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                        PropertyAnnotation pa = lattice.getPropertyAnnotation(invariant.getType());
                        if (!pa.getAnnotationType().isTrivial()) {
                            Condition inv = new Condition(
                                    true,
                                    ConditionLocation.INVARIANT_STATIC,
                                    pa,
                                    containingClassName + "." + invariant.getFieldName()
                            );
                            printlnAligned(inv);
                        }
                    }

                    for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                        PropertyAnnotation pa = lattice.getPropertyAnnotation(invariant.getType());
                        if (!pa.getAnnotationType().isTrivial()) {
                            Condition inv = new Condition(
                                    true,
                                    ConditionLocation.INVARIANT_INSTANCE,
                                    pa,
                                    invariant.getFieldName()
                            );
                            printlnAligned(inv.toStringOp("packed <: " + containingClassName, "==>"));
                        }
                    }
                }

                println();

                for (JCTree def : tree.defs) {
                    align();
                    def.accept(this);
                    println();
                }

                undent();
                printlnAligned("}");
            }

            enclClass = enclClassPrev;
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitMethodDef(JCMethodDecl tree) {
        try {
            // omit anonymous constructors
            if (tree.name == tree.name.table.names.init && enclClass == null) {
                return;
            }
            println();
            if (docComments != null && docComments.getCommentText(tree) != null) {
                align();
                printDocComment(tree);
            }

            JCMethodDecl prevEnclMethod = enclMethod;
            enclMethod = tree;

            JMLContract jmlContract = new JMLContract(Flags.asFlagSet(tree.mods.flags));
            jmlContract.addClause("diverges true;");

            List<String> paramNames = tree.params.stream().map(JCVariableDecl::getName).map(Object::toString).collect(Collectors.toList());
            {
                List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
                List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);
                AnnotationMirror receiverInputType = inputPackingTypes.get(0);
                AnnotationMirror receiverOutputType = outputPackingTypes.get(0);

                if (receiverInputType != null) {
                    jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(receiverInputType, "this")));
                }

                if (receiverOutputType != null) {
                    jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(receiverOutputType, "this")));
                }

                for (int i = 0; i < paramNames.size(); ++i) {
                    if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                        jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(inputPackingTypes.get(i + 1), paramNames.get(i))));
                        jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(outputPackingTypes.get(i + 1), paramNames.get(i))));
                    }
                }
            }

            for (LatticeVisitor.Result wellTypedness : results) {
                LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                Lattice lattice = factory.getLattice();
                AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);

                if (method.getReceiverType() != null) {
                    AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredReceiverType);
                    jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this"));
                }

                for (int i = 0; i < method.getParameterTypes().size(); ++i) {
                    AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                    String paramName = paramNames.get(i);


                    if (!AnnotationUtils.areSame(paramType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                        jmlContract.addClause(
                                new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, lattice.getPropertyAnnotation(paramType), paramName));
                    }
                }
            }

            if (isConstructor(tree)) {
                for (LatticeVisitor.Result wellTypedness : results) {
                    LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                    AnnotatedTypeMirror receiverType = factory.getMethodReturnType(enclMethod);

                    if (AnnotationUtils.areSame(receiverType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                        continue;
                    }

                    Lattice lattice = wellTypedness.getLattice();
                    boolean wt = wellTypedness.isWellTypedConstructor(tree);

                    PropertyAnnotation pa = lattice.getPropertyAnnotation(receiverType);
                    jmlContract.addClause(new Condition(wt, ConditionLocation.POSTCONDITION, pa, "this"));
                    if (!wt) {
                        ++assertions;
                    }
                }
            } else {
                for (LatticeVisitor.Result wellTypedness : results) {
                    Lattice lattice = wellTypedness.getLattice();
                    LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                    AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

                    if (!(returnType instanceof AnnotatedExecutableType)
                            && returnType.getKind() != TypeKind.VOID
                            && !AnnotationUtils.areSame(returnType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                        boolean wt = wellTypedness.isWellTypedMethodResult(tree);
                        PropertyAnnotation pa = lattice.getPropertyAnnotation(returnType);
                        jmlContract.addClause(new Condition(wt, ConditionLocation.POSTCONDITION, pa, "\\result"));

                        if (!wt) {
                            ++methodCallPostconditions;
                        } else {
                            ++freeMethodCallPostconditions;
                        }
                    }
                }
            }

            for (LatticeVisitor.Result wellTypedness : results) {
                Lattice lattice = wellTypedness.getLattice();
                LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
                Set<Integer> illTypedMethodOutputParams = wellTypedness.getIllTypedMethodOutputParams(tree);
                {
                    AnnotationMirror paramOutputType = methodOutputTypes.get(0);
                    String paramName = "this";
                    boolean wt = !illTypedMethodOutputParams.contains(0);

                    if (paramOutputType != null && !AnnotationUtils.areSame(paramOutputType, factory.getTop())) {
                        jmlContract.addClause(
                                new Condition(
                                        wt,
                                        ConditionLocation.POSTCONDITION,
                                        lattice.getPropertyAnnotation(paramOutputType),
                                        paramName));

                        if (!wt) {
                            ++methodCallPostconditions;
                        } else {
                            ++freeMethodCallPostconditions;
                        }
                    }
                }
                for (int i = 0; i < method.getParameterTypes().size(); ++i) {
                    AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                    String paramName = paramNames.get(i);
                    boolean wt = !illTypedMethodOutputParams.contains(i + 1);

                    if (!AnnotationUtils.areSame(paramOutputType, factory.getTop())) {
                        jmlContract.addClause(
                                new Condition(
                                        wt,
                                        ConditionLocation.POSTCONDITION,
                                        lattice.getPropertyAnnotation(paramOutputType),
                                        paramName));

                        if (!wt) {
                            ++methodCallPostconditions;
                        } else {
                            ++freeMethodCallPostconditions;
                        }
                    }
                }
            }

            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();
            
            getJMLClauseValues(element).forEach(jmlContract::addClause);
            if (TRANSLATION_RAW) {
                getJMLClauseValuesTranslationOnly(element).forEach(jmlContract::addClause);
            }
            
            printlnAligned(jmlContract.toString());

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
            } else {
                TypeKind k = propertyFactory.getAnnotatedType(tree).getReturnType().getKind();
                if (k != TypeKind.VOID && !k.isPrimitive()) {
                    print("/*@nullable@*/ ");
                }
                printExpr(tree.restype);
                print(" " + tree.name);
            }

            print("(");

            StringJoiner paramsStr = new StringJoiner(", ");
            for (JCVariableDecl param : tree.params) {
                paramsStr.add(unannotatedNullableTypeName(param) + " " + param.getName());
            }
            print(paramsStr);


            print(")");

            if (tree.thrown.nonEmpty()) {
                print(" throws ");
                printExprs(tree.thrown);
            }

            if (tree.defaultValue != null) {
                print(" default ");
                printExpr(tree.defaultValue);
            }

            if (tree.body != null) {
                println(" {");
                indent();

                if (isConstructor(tree)) {
                    // super constructor call
                    align();
                    printStat(tree.body.stats.get(0));
                    println();

                    printInstanceInitializers();
                    println();

                    for (int i = 1; i < tree.body.stats.size(); ++i) {
                        JCStatement statement = tree.body.stats.get(i);

                        align();
                        printStat(statement);
                        println();
                    }
                } else {
                    for (JCStatement statement : tree.body.stats) {
                        align();
                        printStat(statement);
                        println();
                    }
                }

                undent();
                printlnAligned("}");
            } else {
                print(";");
            }

            enclMethod = prevEnclMethod;

            if (!isInterface(enclClass) && !(isAbstract(enclClass) && isConstructor(tree))) {
                println();
                printTrampoline(tree);
            } else if (isInterface(enclClass)) {
                printTrampoline(tree, false);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

	@Override
    public void visitBlock(JCBlock tree) {
        boolean prevEnclBlock = enclBlock;
        if (enclMethod != null || enclBlock) {
            enclBlock = true;
            try {
                printBlock(tree.stats);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
        enclBlock = prevEnclBlock;
    }

    @Override
    public void visitModifiers(JCModifiers mods) {
        try {
            printFlags(mods.flags);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitNewClass(JCNewClass tree) {
        try {
            if (tree.encl != null) {
                printExpr(tree.encl);
                print(".");
            }

            if (tree.def != null && tree.def.mods.annotations.nonEmpty()) {
                printTypeAnnotations(tree.def.mods.annotations);
            }
            print(tree.clazz.toString());
            print(".");
            print(trampolineName("<init>"));
            print("(");

            AnnotatedExecutableType invokedMethod = propertyFactory.constructorFromUse(tree).executableType;
            StringJoiner args = new StringJoiner(", ");
            args.add(tree.args.toString());

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().constructorFromUse(tree).executableType;

                for (int i = 0; i < invokedMethod.getParameterTypes().size(); ++i) {
                    if (!wellTypedness.getLattice().getPropertyAnnotation(methodType.getParameterTypes().get(i)).getAnnotationType().isTrivial()) {
                        args.add(wellTypedness.getIllTypedConstructorParams(tree).contains(i) || TRANSLATION_RAW ? "false" : "true");
                    }
                }
            }

            print(args);

            print(")");
            if (tree.def != null) {
                com.sun.tools.javac.util.Name enclClassNamePrev = enclClassName;
                enclClassName =
                        tree.def.name != null ? tree.def.name :
                            tree.type != null && tree.type.tsym.name != tree.type.tsym.name.table.names.empty
                                ? tree.type.tsym.name : null;
                if ((tree.def.mods.flags & Flags.ENUM) != 0) {
                    print("/*enum*/");
                }
                printBlock(tree.def.defs);
                enclClassName = enclClassNamePrev;
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitApply(JCMethodInvocation tree) {
        if (tree.meth.toString().equals("super") || tree.meth.toString().equals("this")) {
            super.visitApply(tree);
            return;
        }

        try {
            if (tree.meth.toString().equals("Packing.pack")) {
                AssertionSequence assertionsSeq = new AssertionSequence();

                println();
                for (LatticeVisitor.Result result : results) {
                    List<VariableElement> allFields = ElementFilter.fieldsIn(TypesUtils.getTypeElement(enclClass.type).getEnclosedElements());
                    List<VariableElement> uninitFields = result.getUninitializedFields(tree);
                    for (VariableElement field : allFields) {
                        if (!field.asType().getKind().isPrimitive()) {
                            printlnAligned(String.format(
                                    "//@ assume %s;",
                                    getPackedCondition(
                                            propertyFactory.getAnnotatedType(field).getAnnotationInHierarchy(propertyFactory.getInitialized()),
                                            field.getSimpleName().toString())));
                        }

                        AnnotatedTypeMirror type = result.getTypeFactory().getAnnotatedType(field);
                        PropertyAnnotation pa = result.getLattice().getPropertyAnnotation(type);
                        if (!pa.getAnnotationType().isTrivial()) {
                            Condition cond = new Condition(
                                    !uninitFields.contains(field),
                                    ConditionLocation.ASSERTION,
                                    pa,
                                    field.toString());
                            assertionsSeq.addClause(cond);
                        }
                    }
                }
                
                printlnAligned(assertionsSeq.toString());
                assertions += assertionsSeq.assertions.size();
                align();
                TypeElement typeElement = (TypeElement) TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression());
                //TODO Workaround for KeY not supporting set statement for \TYPE variable because Recoder is terrible
                //print(String.format("//@ set packed = \\type(%s)", typeElement));
                print(String.format("havocPacked(); //@ assume packed == \\type(%s)", typeElement));
                return;
            }

            if (tree.meth.toString().equals("Packing.unpack")) {
                TypeElement typeElement = (TypeElement) TreeUtils.elementFromUse(((MemberSelectTree) tree.args.get(1)).getExpression());
                //TODO Workaround for KeY not supporting set statement for \TYPE variable because Recoder is terrible
                //print(String.format("//@ set packed = \\type(%s)", typeElement.getSuperclass()));
                print(String.format("havocPacked(); //@ assume packed == \\type(%s)", typeElement.getSuperclass()));
                return;
            }

            AnnotatedExecutableType invokedMethod = propertyFactory.methodFromUse(tree).executableType;
            StringJoiner booleanArgs = new StringJoiner(", ");

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().methodFromUse(tree).executableType;

                if (!ElementUtils.isStatic(invokedMethod.getElement())) {
                    if (!wellTypedness.getLattice().getPropertyAnnotation(methodType.getReceiverType()).getAnnotationType().isTrivial()) {
                    	if (wellTypedness.getIllTypedMethodReceivers().contains(tree) || TRANSLATION_RAW ) {
                    		booleanArgs.add("false");
                    		++methodCallPreconditions;
                    	} else {
                    		booleanArgs.add("true");
                    		++freeMethodCallPreconditions;
                    	}
                    }
                }

                for (int i = 0; i < invokedMethod.getParameterTypes().size(); ++i) {
                    if (!wellTypedness.getLattice().getPropertyAnnotation(methodType.getParameterTypes().get(i)).getAnnotationType().isTrivial()) {
                    	if (wellTypedness.getIllTypedMethodParams(tree).contains(i) || TRANSLATION_RAW) {
                    		booleanArgs.add("false");
                    		++methodCallPreconditions;
                    	} else {
                    		booleanArgs.add("true");
                    		++freeMethodCallPreconditions;
                    	}
                    }
                }
            }
            
            if (booleanArgs.length() == 0) {
                super.visitApply(tree);
                return;
            }
            
            if (tree.meth.hasTag(SELECT)) {
                JCFieldAccess left = (JCFieldAccess)tree.meth;
                printExpr(left.selected);
                print(".");
                print(trampolineName(left.name));
            } else {
                print(trampolineName(tree.meth.toString()));
            }

            print("(");
            printExprs(tree.args);

            if (!tree.args.isEmpty() && booleanArgs.length() != 0) {
                print(", ");
            }
            print(booleanArgs);

            print(")");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void visitAssign(JCAssign tree) {
        // Only assignments to local variables need an assertion; fields are checked at the next packing statement.
        if (tree.getVariable() instanceof MemberSelectTree) {
            super.visitAssign(tree);
            return;
        }

        String tempVar = tempVarName();

        visitAssignOrDef(
                tree.getVariable().toString(),
                unannotatedTypeNameLhs(tree.getVariable()),
                tree.getExpression(),
                getConditions(tree, tempVar, ConditionLocation.ASSERTION),
                tempVar);
    }

    @Override
    public void visitVarDef(JCVariableDecl tree) {
        if (enclMethod == null) {
            try {
                print("public ");
                if (tree.getModifiers().getFlags().contains(Modifier.STATIC)) {
                    print("static ");
                }
                println(String.format("%s %s;", unannotatedNullableTypeNameLhs(tree), tree.getName()));
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
            return;
        }

        try {
            String tempVar = tempVarName();

            print(String.format("%s %s", unannotatedTypeNameLhs(tree), tree.getName()));
            if (prec == TreeInfo.notExpression) {
                println(";");
                align();
            }

            if (tree.getInitializer() != null) {
                visitAssignOrDef(
                        tree.getName().toString(),
                        unannotatedTypeNameLhs(tree),
                        tree.getInitializer(),
                        getConditions(tree, tempVar, ConditionLocation.ASSERTION),
                        tempVar);
                print(";");
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void visitAssignNoConditions(String varName, JCTree expression) {
        try {
            print(String.format("%s = ", varName));
            expression.accept(this);
            println(";");
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void visitAssignOrDef(String varName, String unannotatedTypeName, JCTree expression, List<Condition> conditions, String tempVar) {
        try {
            print(String.format("%s %s = ", unannotatedTypeName, tempVar));
            expression.accept(this);
            println(";");

            for (Condition condition : conditions) {
                printlnAligned(condition);
                
                if (!condition.pa.getAnnotationType().isTrivial()) {
                    if (condition.conditionType == ConditionType.ASSERTION || TRANSLATION_RAW) {
                    	++assertions;
                    } else {
                    	++assumptions;
                    }
                }
            }

            align();
            print(String.format("%s = %s", varName, tempVar));
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void printStaticInitializers() throws IOException {
        List<Union<StatementTree, VariableTree, BlockTree>> inits =
                results.get(0).getStaticInitializers(enclClass.sym.getQualifiedName().toString());
        
        if (inits.isEmpty()) {
            return;
        }
        
        printlnAligned("static {");
        indent();
        enclBlock = true;
        
        for (Union<StatementTree, VariableTree, BlockTree> init : inits) {
            align();
            init.consume(
                    var -> {
                        if (var.getInitializer() != null) {
                            String tempVar = tempVarName();

                            visitAssignOrDef(
                                    var.getName().toString(),
                                    unannotatedTypeNameLhs((JCVariableDecl) var),
                                    (JCTree) var.getInitializer(),
                                    getConditions((JCVariableDecl) var, tempVar, ConditionLocation.ASSERTION),
                                    tempVar);
                            try {
                                println(";");
                            } catch (IOException e) {
                                throw new AssertionError();
                            }
                        }
                    },
                    block -> {
                        ((JCBlock) block).accept(this);
                    });
            println();
        }

        enclBlock = false;
        undent();
        printlnAligned("}");
        println();
    }

    protected void printInstanceInitializers() throws IOException {
        List<Union<StatementTree, VariableTree, BlockTree>> inits =
                results.get(0).getInstanceInitializers(enclClass.sym.getQualifiedName().toString());
        for (Union<StatementTree, VariableTree, BlockTree> init : inits) {
            align();
            init.consume(
                    var -> {
                        visitAssignNoConditions(
                                var.getName().toString(),
                                (JCTree) var.getInitializer());
                    },
                    block -> {
                        ((JCBlock) block).accept(this);
                    });
            println();
        }
    }

    protected void printTrampoline(JCMethodDecl tree) {
        printTrampoline(tree, true);
    }
    
    protected void printTrampoline(JCMethodDecl tree, boolean printBody) {
        List<String> paramNames = tree.getParameters().stream().map(JCVariableDecl::getName).map(Object::toString).collect(Collectors.toList());

        StringJoiner paramStr = new StringJoiner(", ");
        for (int i = 0; i < paramNames.size(); ++i) {
            paramStr.add(String.format("%s %s", unannotatedNullableTypeNameLhs(tree.getParameters().get(i)), paramNames.get(i)));
        }
        for (LatticeVisitor.Result wellTypedness : results) {
            AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().getAnnotatedType(tree);
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
            List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

            if (requiredReceiverType != null
                    && !lattice.getPropertyAnnotation(requiredReceiverType).getAnnotationType().isTrivial()) {
                paramStr.add(String.format("boolean %s", trampolineBooleanParamName("this", wellTypedness)));
            }

            for (int i = 0; i < paramNames.size(); ++i) {
                if (!lattice.getPropertyAnnotation(requiredParamTypes.get(i)).getAnnotationType().isTrivial()) {
                    paramStr.add(String.format("boolean %s", trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                }
            }
        }

        AnnotatedExecutableType propertyMethodType = propertyFactory.getAnnotatedType(tree);

        JMLContract jmlContract = new JMLContract(EnumSet.of(Flag.PUBLIC));
        jmlContract.addClause("diverges true;");

        {
            List<AnnotationMirror> inputPackingTypes = propertyFactory.getInputPackingTypes(tree);
            List<AnnotationMirror> outputPackingTypes = propertyFactory.getOutputPackingTypes(tree);
            AnnotationMirror receiverInputType = inputPackingTypes.get(0);
            AnnotationMirror receiverOutputType = outputPackingTypes.get(0);

            if (receiverInputType != null) {
                jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(receiverInputType, "this")));
            }

            if (receiverOutputType != null) {
                jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(receiverOutputType, "this")));
            }

            for (int i = 0; i < paramNames.size(); ++i) {
                if (!tree.getParameters().get(i).type.getKind().isPrimitive()) {
                    jmlContract.addClause(String.format("requires_free %s;", getPackedCondition(inputPackingTypes.get(i + 1), paramNames.get(i))));
                    jmlContract.addClause(String.format("ensures_free %s;", getPackedCondition(outputPackingTypes.get(i + 1), paramNames.get(i))));
                }
            }
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);
            List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

            if (methodType.getReceiverType() != null) {
                AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
                PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredReceiverType);
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial()) {
                    jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this")
                            .toStringOr(trampolineBooleanParamName("this", wellTypedness)));
                    jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, "this")
                            .toStringOr("!" + trampolineBooleanParamName("this", wellTypedness)));
                }
            }

            for (int i = 0; i < requiredParamTypes.size(); ++i) {
                PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                PropertyAnnotationType pat = pa.getAnnotationType();

                if (!pat.isTrivial()
                        && !AnnotationUtils.areSame(requiredParamTypes.get(i).getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                    jmlContract.addClause(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                            .toStringOr(trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                    jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                            .toStringOr("!" + trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                }
            }
        }

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            Lattice lattice = wellTypedness.getLattice();

            AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);
            List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

            if (methodType.getReceiverType() != null) {
                AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
                PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredReceiverType);
                jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, "this"));
            }

            for (int i = 0; i < requiredParamTypes.size(); ++i) {
                PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, paramNames.get(i)));
            }
        }


        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            Lattice lattice = wellTypedness.getLattice();
            AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID && !isConstructor(tree)) {
                AnnotatedTypeMirror returnType = wellTypedness.getTypeFactory().getMethodReturnType(tree);
                AnnotationMirror anno = returnType.getAnnotationInHierarchy(wellTypedness.getTypeFactory().getTop());

                if (anno != null && !AnnotationUtils.areSame(
                        anno,
                        wellTypedness.getTypeFactory().getTop())) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(returnType);
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if (pat.isTrivial()) {
                        continue;
                    }

                    jmlContract.addClause(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, "\\result").toString());
                }
            }

            List<AnnotationMirror> methodOutputTypes = wellTypedness.getMethodOutputTypes(tree);
            {
                AnnotationMirror paramOutputType = methodOutputTypes.get(0);

                if (paramOutputType != null && !AnnotationUtils.areSame(paramOutputType, factory.getTop())) {
                    jmlContract.addClause(
                            new Condition(
                                    true,
                                    ConditionLocation.POSTCONDITION,
                                    lattice.getPropertyAnnotation(paramOutputType),
                                    "this"));
                }
            }
            for (int i = 0; i < methodType.getParameterTypes().size(); ++i) {
                AnnotationMirror paramOutputType = methodOutputTypes.get(i + 1);
                String paramName = paramNames.get(i);

                if (!AnnotationUtils.areSame(paramOutputType, factory.getTop())) {
                    jmlContract.addClause(
                            new Condition(
                                    true,
                                    ConditionLocation.POSTCONDITION,
                                    lattice.getPropertyAnnotation(paramOutputType),
                                    paramName));
                }
            }
        }

        if (isConstructor(tree)) {
            jmlContract.addClause("ensures \\result != null && \\fresh(\\result);");
        }

        ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

        for (String clause : getJMLClauseValues(element)) {
            if (isConstructor(tree) && clause.startsWith("assignable")) {
                jmlContract.addClause(clause.replace("this.*", "\\nothing"));
            } else {
                jmlContract.addClause(clause);
            }
        }

        if (TRANSLATION_RAW) {
            for (String clause : getJMLClauseValuesTranslationOnly(element)) {
                if (isConstructor(tree) && clause.startsWith("assignable")) {
                    jmlContract.addClause(clause.replace("this.*", "\\nothing"));
                } else {
                    jmlContract.addClause(clause);
                }
            }
        }

        if (isConstructor(tree)) {
            printlnAligned(jmlContract.toString().replace("this", "\\result"));
        } else {
            printlnAligned(jmlContract.toString());
        }

        if (printBody) {
            printlnAligned(String.format("public %s %s%s %s(%s) {",
                    ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                            propertyMethodType.getReturnType().getKind() == TypeKind.VOID || propertyMethodType.getReturnType().getKind().isPrimitive()
                            ? "" : "/*@nullable@*/ ",
                                    TypeUtils.unannotatedTypeName(propertyMethodType.getReturnType()),
                                    trampolineName(tree.getName()),
                                    paramStr));

            indent();

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID) {
                printlnAligned(String.format(
                        "return %s(%s);",
                        tree.getName().toString().equals("<init>") ? ("new " + getEnclClassName()) : tree.getName(),
                                String.join(", ", paramNames)
                        ));
            } else {
                printlnAligned(String.format("%s(%s);", tree.getName(), String.join(", ", paramNames)));
            }

            undent();
            printlnAligned("}");
        } else {
            printlnAligned(String.format("public %s %s%s %s(%s);",
                    ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                            propertyMethodType.getReturnType().getKind() == TypeKind.VOID || propertyMethodType.getReturnType().getKind().isPrimitive()
                            ? "" : "/*@nullable@*/ ",
                                    TypeUtils.unannotatedTypeName(propertyMethodType.getReturnType()),
                                    trampolineName(tree.getName()),
                                    paramStr));
        }
    }

    protected void printlnAligned(Condition cond) {
        PropertyAnnotationType pat = cond.pa.getAnnotationType();

        if (pat.isTrivial()) {
            return;
        }

        printlnAligned(cond.toString());
    }

    protected void printlnAligned(String s) {
        for (String line : s.lines().collect(Collectors.toList())) {
            try {
                align();
                println(line);
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
    }

    protected void println(Condition cond) throws IOException {
        PropertyAnnotationType pat = cond.pa.getAnnotationType();

        if (pat.isTrivial()) {
            return;
        }

        println(cond.toString());
    }

    protected void println(String s) throws IOException {
        print(s + StringUtils.LF);
    }

    protected void print() throws IOException {
        print(StringUtils.EMPTY);
    }

    protected boolean isAbstract(JCClassDecl tree) {
        return (tree.mods.flags & ABSTRACT) != 0;
    }

    protected boolean isInterface(JCClassDecl tree) {
        return (tree.mods.flags & INTERFACE) != 0;
    }

    protected boolean isConstructor(JCMethodDecl tree) {
        return tree.name == tree.name.table.names.init;
    }

    protected String trampolineName(String methodName) {
        if (methodName.equals("<init>")) {
            methodName = "INIT";
        }

        return String.format("__%s_trampoline", methodName.replace('.', '_'));
    }

    protected String trampolineName(Name methodName) {
        return trampolineName(methodName.toString());
    }

    protected String trampolineBooleanParamName(String paramName, LatticeVisitor.Result wellTypedness) {
        return String.format("%s_%s", paramName, wellTypedness.getTypeFactory().getLattice().getIdent());
    }


    protected String unannotatedTypeName(JCTree tree) {
        return TypeUtils.unannotatedTypeName(results.get(0).getTypeFactory().getAnnotatedType(tree));
    }

    protected String unannotatedNullableTypeName(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedType(tree);

        return (type.getKind() == TypeKind.VOID || type.getKind().isPrimitive()
        		? "" : "/*@nullable@*/ ")
                + TypeUtils.unannotatedTypeName(type);
    }

    protected String unannotatedTypeNameLhs(JCTree tree) {
        return TypeUtils.unannotatedTypeName(results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree));
    }

    protected String unannotatedNullableTypeNameLhs(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree);

        return (type.getKind() == TypeKind.VOID || type.getKind().isPrimitive()
        		? "" : "/*@nullable@*/ ")
                + TypeUtils.unannotatedTypeName(type);
    }

    protected String unannotatedReturnTypeName() {
        return TypeUtils.unannotatedTypeName(results.get(0).getTypeFactory().getMethodReturnType(enclMethod));
    }

    protected String tempVarName() {
        return String.format("temp%d", tempVarNum++);
    }

    public Name getEnclClassName() {
        return enclClass.sym.getQualifiedName();
    }

    public Name getEnclMethodNameName() {
        return enclMethod.sym.getQualifiedName();
    }
    
    @SuppressWarnings("unchecked")
    protected List<String> getJMLClauseValues(ExecutableElement element) {
        AnnotationMirror jmlClauses = propertyFactory.getDeclAnnotation(element, JMLClauses.class);
        AnnotationMirror jmlClause = propertyFactory.getDeclAnnotation(element, JMLClause.class);
        
        if (jmlClauses == null && jmlClause == null) {
            return Collections.emptyList();
        } else if (jmlClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(jmlClauses, "value", List.class, true).stream()
                .map(o -> {
                    String s = ((Attribute.Compound) o).values.head.snd.toString();
                    return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                })
                .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(jmlClause, "value", String.class, true));
        }
    }
    
    @SuppressWarnings("unchecked")
    protected List<String> getJMLClauseValuesTranslationOnly(ExecutableElement element) {
        AnnotationMirror jmlClauses = propertyFactory.getDeclAnnotation(element, JMLClausesTranslationOnly.class);
        AnnotationMirror jmlClause = propertyFactory.getDeclAnnotation(element, JMLClauseTranslationOnly.class);
        
        if (jmlClauses == null && jmlClause == null) {
            return Collections.emptyList();
        } else if (jmlClauses != null) {
            return (List<String>) AnnotationUtils.getElementValue(jmlClauses, "value", List.class, true).stream()
                .map(o -> {
                    String s = ((Attribute.Compound) o).values.head.snd.toString();
                    return s.substring(1, s.length() - 1).replace("\\\\", "\\");
                })
                .collect(Collectors.toList());
        } else {
            return Collections.singletonList(AnnotationUtils.getElementValue(jmlClause, "value", String.class, true));
        }
    }

    protected List<Condition> getConditions(JCAssign tree, String subject, ConditionLocation conditionLocation) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree.getVariable());

            if (type instanceof AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getPropertyAnnotation(type);
            (wt ? wellTyped : malTyped).add(new Condition(wt, conditionLocation, pa, subject));
        }

        return Streams.concat(wellTyped.stream(), malTyped.stream()).collect(Collectors.toList());
    }

    protected List<Condition> getConditions(JCVariableDecl tree, String subject, ConditionLocation conditionLocation) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror type = factory.getAnnotatedTypeLhs(tree);

            if (type instanceof AnnotatedExecutableType
                    || AnnotationUtils.areSame(type.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getPropertyAnnotation(factory.getAnnotatedTypeLhs(tree));
            (wt ? wellTyped : malTyped).add(new Condition(wt, conditionLocation, pa, subject));
        }

        return Streams.concat(wellTyped.stream(), malTyped.stream()).collect(Collectors.toList());
    }

    protected Object getVisibilityString(EnumSet<Flag> flagSet) {
		if (flagSet.contains(Flag.PUBLIC)) {
			return "public";
		} else if (flagSet.contains(Flag.PROTECTED)) {
			return "protected";
		} else if (flagSet.contains(Flag.PRIVATE)) {
			return "private";
		} else {
			return "";
		}
	}

    protected String getPackedCondition(AnnotationMirror packingType, String varName) {
        if (propertyFactory.isInitialized(packingType)) {
            return String.format("%s.packed == \\typeof(%s)", varName, varName);
        } else if (propertyFactory.isUnderInitialization(packingType)) {
            return String.format("%s.packed == %s", varName, propertyFactory.getTypeFrameFromAnnotation(packingType));
        } else {
            return String.format("%s.packed <: %s", varName, propertyFactory.getTypeFrameFromAnnotation(packingType));
        }
    }

    public enum ConditionLocation {
        ASSERTION, PRECONDITION, POSTCONDITION, INVARIANT_INSTANCE, INVARIANT_STATIC;
    }

    public enum ConditionType {
        ASSERTION, ASSUMPTION;
    }

    public class Condition {

        protected ConditionLocation conditionLocation;
        protected ConditionType conditionType;
        protected PropertyAnnotation pa;
        protected String subject;
        
        public Condition(boolean wt, ConditionLocation conditionLocation, PropertyAnnotation pa, String subject) {
            this(wt ? ConditionType.ASSUMPTION : ConditionType.ASSERTION, conditionLocation, pa, subject);
        }

        public Condition(ConditionType conditionType, ConditionLocation conditionLocation, PropertyAnnotation pa, String subject) {
            this.conditionType = conditionType;
            this.conditionLocation = conditionLocation;
            this.pa = pa;
            this.subject = subject;
        }

        @Override
        public String toString() {
            return toStringAnd(null);
        }

        public String toStringAnd(String additionalCondition) {
            return toStringOp(additionalCondition, "&&");
        }

        public String toStringOr(String additionalCondition) {
            return toStringOp(additionalCondition, "||");
        }

        protected String toStringOp(String additionalCondition, String op) {
            PropertyAnnotationType pat = pa.getAnnotationType();

            StringBuilder sb = new StringBuilder();

            switch(conditionLocation) {
            case ASSERTION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ assert ");
                    break;
                case ASSUMPTION:
                    sb.append(TRANSLATION_RAW ? "//@ assert " :"//@ assume ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case PRECONDITION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("requires ");
                    break;
                case ASSUMPTION:
                    sb.append("requires_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case POSTCONDITION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("ensures ");
                    break;
                case ASSUMPTION:
                    sb.append(TRANSLATION_RAW ? "ensures " : "ensures_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case INVARIANT_INSTANCE:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ public invariant ");
                    break;
                case ASSUMPTION:
                    sb.append("//@ public invariant_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case INVARIANT_STATIC:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("//@ public static invariant ");
                    break;
                case ASSUMPTION:
                    sb.append("//@ public static invariant_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            }

            if (additionalCondition != null) {
                sb.append(additionalCondition);
                sb.append(" ");
                sb.append(op);
                sb.append(" (");
            }

            sb.append(JavaJMLPrinter.printCheckable(pat.getWellFormednessCheckable(), pa, null));
            sb.append(" && ");

            sb.append(JavaJMLPrinter.printCheckable(pat.getPropertyCheckable(), pa, subject));

            if (additionalCondition != null) {
                sb.append(")");
            }

            sb.append(";");

            return sb.toString();
        }
    }

    public class AssertionSequence {

        private List<String> assertions = new ArrayList<>();
        private List<String> assumptions = new ArrayList<>();

        public void addClause(Condition condition) {
            if (condition.pa.getAnnotationType().isTrivial()) {
                return;
            }

            switch (condition.conditionLocation) {
                case PRECONDITION:
                case POSTCONDITION:
                    throw new IllegalArgumentException("condition");
                case ASSERTION:
                    switch (condition.conditionType) {
                        case ASSERTION:
                            assertions.add(condition.toString());
                            break;
                        case ASSUMPTION:
                            assumptions.add(condition.toString());
                            break;
                    }
                    break;
            }
        }

        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            assumptions.forEach(c -> sb.append(String.format("%s\n", c)));
            assertions.forEach(c -> sb.append(String.format("%s\n", c)));
            return sb.toString();
        }
    }
    
    public class JMLContract {
        
        private EnumSet<Flag> flags;

        private List<String> requiresClauses = new ArrayList<>();
        private List<String> requiresFreeClauses = new ArrayList<>();
        private List<String> ensuresClauses = new ArrayList<>();
        private List<String> ensuresFreeClauses = new ArrayList<>();
        private List<String> otherClauses = new ArrayList<>();
        
        public JMLContract(EnumSet<Flag> flags) {
            this.flags = flags;
        }

        public void addClause(Condition condition) {
            if (condition.pa.getAnnotationType().isTrivial()) {
                return;
            }
            
            switch (condition.conditionLocation) {
            case PRECONDITION:
                switch (condition.conditionType) {
                case ASSERTION:
                    requiresClauses.add(condition.toString());
                    break;
                case ASSUMPTION:
                    requiresFreeClauses.add(condition.toString());
                    break;
                }
                break;
            case POSTCONDITION:
                switch (condition.conditionType) {
                case ASSERTION:
                    ensuresClauses.add(condition.toString());
                    break;
                case ASSUMPTION:
                    ensuresFreeClauses.add(condition.toString());
                    break;
                }
                break;
            case ASSERTION:
                throw new IllegalArgumentException("condition");
            }
        }
        
        public void addClause(String clause) {
            String clauseKind = clause.strip().split("\\s+")[0];
            switch (clauseKind) {
            case "requires":
                requiresClauses.add(clause);
                break;
            case "requires_free":
                requiresFreeClauses.add(clause);
                break;
            case "ensures":
                ensuresClauses.add(clause);
                break;
            case "ensures_free":
                ensuresFreeClauses.add(clause);
                break;
            default:
                otherClauses.add(clause);
                break;
            }
        }
        
        @Override
        public String toString() {
            StringBuilder sb = new StringBuilder();
            sb.append(String.format("/*@ %s behavior\n", getVisibilityString(flags)));
            
            requiresClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            requiresFreeClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            ensuresClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            ensuresFreeClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));
            otherClauses.forEach(c -> sb.append(String.format("  @ %s\n", c)));

            sb.append("  @*/");
            return sb.toString();
        }
    }
}
