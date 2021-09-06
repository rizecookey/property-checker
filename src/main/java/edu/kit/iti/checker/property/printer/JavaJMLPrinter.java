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
package edu.kit.iti.checker.property.printer;

import static com.sun.tools.javac.code.Flags.ABSTRACT;
import static com.sun.tools.javac.code.Flags.ENUM;
import static com.sun.tools.javac.code.Flags.INTERFACE;
import static com.sun.tools.javac.tree.JCTree.Tag.SELECT;

import java.io.BufferedWriter;
import java.io.IOException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.EnumSet;
import java.util.List;
import java.util.Objects;
import java.util.StringJoiner;
import java.util.stream.Collectors;

import javax.lang.model.element.AnnotationMirror;
import javax.lang.model.element.ElementKind;
import javax.lang.model.element.ExecutableElement;
import javax.lang.model.element.Modifier;
import javax.lang.model.element.Name;
import javax.lang.model.type.TypeKind;

import org.apache.commons.lang3.StringUtils;
import org.checkerframework.checker.initialization.qual.Initialized;
import org.checkerframework.framework.type.AnnotatedTypeMirror;
import org.checkerframework.framework.type.AnnotatedTypeMirror.AnnotatedExecutableType;
import org.checkerframework.javacutil.AnnotationUtils;
import org.checkerframework.javacutil.ElementUtils;

import com.google.common.collect.Streams;
import com.sun.source.tree.BlockTree;
import com.sun.source.tree.StatementTree;
import com.sun.source.tree.VariableTree;
import com.sun.tools.javac.code.Attribute;
import com.sun.tools.javac.code.Flags;
import com.sun.tools.javac.code.Flags.Flag;
import com.sun.tools.javac.tree.JCTree;
import com.sun.tools.javac.tree.JCTree.JCAssign;
import com.sun.tools.javac.tree.JCTree.JCBlock;
import com.sun.tools.javac.tree.JCTree.JCClassDecl;
import com.sun.tools.javac.tree.JCTree.JCFieldAccess;
import com.sun.tools.javac.tree.JCTree.JCImport;
import com.sun.tools.javac.tree.JCTree.JCMethodDecl;
import com.sun.tools.javac.tree.JCTree.JCMethodInvocation;
import com.sun.tools.javac.tree.JCTree.JCModifiers;
import com.sun.tools.javac.tree.JCTree.JCNewClass;
import com.sun.tools.javac.tree.JCTree.JCReturn;
import com.sun.tools.javac.tree.JCTree.JCStatement;
import com.sun.tools.javac.tree.JCTree.JCVariableDecl;
import com.sun.tools.javac.tree.TreeInfo;

import edu.kit.iti.checker.property.checker.PropertyAnnotatedTypeFactory;
import edu.kit.iti.checker.property.checker.PropertyChecker;
import edu.kit.iti.checker.property.checker.qual.JMLClause;
import edu.kit.iti.checker.property.checker.qual.JMLClauseTranslationOnly;
import edu.kit.iti.checker.property.checker.qual.JMLClauses;
import edu.kit.iti.checker.property.checker.qual.JMLClausesTranslationOnly;
import edu.kit.iti.checker.property.config.Config;
import edu.kit.iti.checker.property.lattice.Checkable;
import edu.kit.iti.checker.property.lattice.Lattice;
import edu.kit.iti.checker.property.lattice.PropertyAnnotation;
import edu.kit.iti.checker.property.lattice.PropertyAnnotationType;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeAnnotatedTypeFactory;
import edu.kit.iti.checker.property.subchecker.lattice.LatticeVisitor;
import edu.kit.iti.checker.property.util.TypeUtils;
import edu.kit.iti.checker.property.util.Union;

@SuppressWarnings("nls")
public class JavaJMLPrinter extends PrettyPrinter {
    
    public static JMLDialect TRANSLATION_JML_DIALECT = JMLDialect.KeYJMLDialect;
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
        
        String jmlDialectOption = propertyChecker.getOption(Config.TRANSLATION_JML_DIALECT_OPTION);
        
        if (Objects.equals(jmlDialectOption, Config.TRANSLATION_JML_DIALECT_OPTION_OPENJML)) {
        	TRANSLATION_JML_DIALECT = JMLDialect.OpenJMLDialect;
        }
        
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
    
    @Override
    public void visitImport(JCImport tree) {
    	if (tree.qualid.toString().startsWith("edu.kit.iti.checker.property")) {
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
            //printAnnotations(tree.mods.annotations);
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

                for (JCTree def : tree.defs) {
                    align();
                    def.accept(this);
                    println();
                }

                if (!isInterface(tree)) {
                    printlnAligned("static {");
                    indent();
                    enclBlock = true;
                    printStaticInitializers();
                    enclBlock = false;
                    undent();
                    printlnAligned("}");
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

            try {
                printlnAligned(String.format("/*@ %s behavior", getVisibilityString(Flags.asFlagSet(tree.mods.flags))));

                for (LatticeVisitor.Result wellTypedness : results) {
                    LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                    Lattice lattice = factory.getLattice();
                    AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                    List<String> paramNames = tree.params.stream().map(JCVariableDecl::getName).map(Object::toString).collect(Collectors.toList());
                    String containingClassName = enclClass.sym.getQualifiedName().toString();

                    if (method.getReceiverType() != null) {
                        AnnotatedTypeMirror requiredReceiverType = method.getReceiverType();
                        PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredReceiverType);
                        printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this"));
                    }

                    for (int i = 0; i < method.getParameterTypes().size(); ++i) {
                        AnnotatedTypeMirror paramType = method.getParameterTypes().get(i);
                        String paramName = paramNames.get(i);


                        if (!AnnotationUtils.areSame(paramType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                            printlnAligned(
                                    new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, lattice.getPropertyAnnotation(paramType), paramName));
                        }
                    }

                    if (method.getElement().getKind() != ElementKind.CONSTRUCTOR && TRANSLATION_JML_DIALECT == JMLDialect.KeYJMLDialect) {
                        for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                            printlnAligned(
                                    new Condition(
                                            ConditionType.ASSUMPTION,
                                            ConditionLocation.PRECONDITION,
                                            lattice.getPropertyAnnotation(invariant.getType()), getEnclClassName() + "." + invariant.getFieldName()));
                        }

                        if (!ElementUtils.isStatic(method.getElement()) && (tree.getReceiverParameter() == null
                                || factory.getAnnotatedType(tree.getReceiverParameter()).getAnnotation(Initialized.class) != null)) {
                            for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                                printlnAligned(
                                        new Condition(
                                                ConditionType.ASSUMPTION,
                                                ConditionLocation.PRECONDITION,
                                                lattice.getPropertyAnnotation(invariant.getType()), "this." + invariant.getFieldName()));
                            }
                        }
                    }
                }

                if (isConstructor(tree)) {
                    for (Condition condition : getPostconditionsForConstructor(tree, "this")) {
                        printlnAligned(condition);
                    }
                } else {
                    for (Condition condition : getPostconditionsForMethod(tree, "\\result")) {
                        printlnAligned(condition);
                    }
                }

                ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

                for (String clause : getJMLClauseValues(element)) {
                    printlnAligned(String.format("  @ %s;", clause));
                }

                if (TRANSLATION_RAW) {
                    for (String clause : getJMLClauseValuesTranslationOnly(element)) {
                        printlnAligned(String.format("  @ %s;", clause));
                    }
                }

                printlnAligned("  @ diverges true;");
                printlnAligned("  @*/");
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }

            align();
            printExpr(tree.mods);

            if (isConstructor(tree)) {
                print(enclClass != null ? enclClass.sym.getSimpleName() : tree.name);
            } else {
                if (!ElementUtils.isStatic(propertyFactory.getAnnotatedType(tree).getElement())
                		&& TRANSLATION_JML_DIALECT == JMLDialect.KeYJMLDialect) {
                    print("/*@helper@*/ ");
                }

                TypeKind k = propertyFactory.getAnnotatedType(tree).getReturnType().getKind();
                if (k != TypeKind.VOID && !k.isPrimitive() && TRANSLATION_JML_DIALECT == JMLDialect.KeYJMLDialect) {
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

                for (LatticeVisitor.Result wellTypedness : results) {
                	LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                	Lattice lattice = factory.getLattice();
                	AnnotatedExecutableType method = wellTypedness.getTypeFactory().getAnnotatedType(tree);
                	String containingClassName = enclClass.sym.getQualifiedName().toString();


                	if (method.getElement().getKind() != ElementKind.CONSTRUCTOR && TRANSLATION_JML_DIALECT == JMLDialect.OpenJMLDialect) {
                		for (LatticeVisitor.Invariant invariant : wellTypedness.getStaticInvariants(containingClassName)) {
                			printlnAligned(
                					new Condition(
                							ConditionType.ASSUMPTION,
                							ConditionLocation.ASSERTION,
                							lattice.getPropertyAnnotation(invariant.getType()), getEnclClassName() + "." + invariant.getFieldName()));
                		}

                		if (!ElementUtils.isStatic(method.getElement()) && (tree.getReceiverParameter() == null
                				|| factory.getAnnotatedType(tree.getReceiverParameter()).getAnnotation(Initialized.class) != null)) {
                			for (LatticeVisitor.Invariant invariant : wellTypedness.getInstanceInvariants(containingClassName)) {
                				printlnAligned(
                						new Condition(
                								ConditionType.ASSUMPTION,
                								ConditionLocation.ASSERTION,
                								lattice.getPropertyAnnotation(invariant.getType()), "this." + invariant.getFieldName()));
                			}
                		}
                	}
                }

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
                        args.add(wellTypedness.getMalTypedConstructorParams(tree).contains(i) || TRANSLATION_RAW ? "false" : "true");
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
            if (tree.meth.hasTag(SELECT)) {
                JCFieldAccess left = (JCFieldAccess)tree.meth;
                printExpr(left.selected);
                print(".");
                print(trampolineName(left.name));
            } else {
                print(trampolineName(tree.meth.toString()));
            }

            print("(");

            AnnotatedExecutableType invokedMethod = propertyFactory.methodFromUse(tree).executableType;
            printExprs(tree.args);
            StringJoiner booleanArgs = new StringJoiner(", ");

            for (LatticeVisitor.Result wellTypedness : results) {
                AnnotatedExecutableType methodType = wellTypedness.getTypeFactory().methodFromUse(tree).executableType;

                if (!ElementUtils.isStatic(invokedMethod.getElement())) {
                    if (!wellTypedness.getLattice().getPropertyAnnotation(methodType.getReceiverType()).getAnnotationType().isTrivial()) {
                    	if (wellTypedness.getMalTypedMethodReceivers().contains(tree) || TRANSLATION_RAW ) {
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
                    	if (wellTypedness.getMalTypedMethodParams(tree).contains(i) || TRANSLATION_RAW) {
                    		booleanArgs.add("false");
                    		++methodCallPreconditions;
                    	} else {
                    		booleanArgs.add("true");
                    		++freeMethodCallPreconditions;
                    	}
                    }
                }
            }

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
    public void visitReturn(JCReturn tree) {
        JCTree expression = tree.getExpression();

        if (isConstructor(enclMethod)) {
            super.visitReturn(tree);
        } else {
            try {
                if (expression == null) {
                    println("return;");
                }

                String tempVar = tempVarName();

                print(String.format("%s %s = ", unannotatedReturnTypeName(), tempVar));
                expression.accept(this);
                println(";");

                for (Condition condition : getConditions(tree, tempVar, ConditionLocation.ASSERTION)) {
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
                print(String.format("return %s;", tempVar));
            } catch (IOException e) {
                throw new UncheckedIOException(e);
            }
        }
    }

    @Override
    public void visitAssign(JCAssign tree) {
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
    	if (TRANSLATION_JML_DIALECT == JMLDialect.KeYJMLDialect) {
    		printTrampolineKeY(tree, printBody);
    	} else {
    		printTrampolineOpenJML(tree, printBody);
    	}
    }

    protected void printTrampolineKeY(JCMethodDecl tree, boolean printBody) {
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

        try {
            AnnotatedExecutableType propertyMethodType = propertyFactory.getAnnotatedType(tree);

            printlnAligned("/*@ public behavior");
            
            List<String> nonFreePreconditions = new ArrayList<>();
            List<String> freePreconditions = new ArrayList<>();

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
                        nonFreePreconditions.add(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this")
                                .toStringOr(trampolineBooleanParamName("this", wellTypedness)));
                        freePreconditions.add(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, "this")
                                .toStringOr("!" + trampolineBooleanParamName("this", wellTypedness)));
                    }
                }

                for (int i = 0; i < requiredParamTypes.size(); ++i) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if (!pat.isTrivial()
                            && !AnnotationUtils.areSame(requiredParamTypes.get(i).getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                        nonFreePreconditions.add(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                                .toStringOr(trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                        freePreconditions.add(new Condition(ConditionType.ASSUMPTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                                .toStringOr("!" + trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                    }
                }
            }
            
            for (String s : nonFreePreconditions) {
                printlnAligned(s);
            }
            
            for (String s : freePreconditions) {
                printlnAligned(s);
            }

            for (LatticeVisitor.Result wellTypedness : results) {
                LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
                Lattice lattice = wellTypedness.getLattice();

                AnnotatedExecutableType methodType = factory.getAnnotatedType(tree);
                List<AnnotatedTypeMirror> requiredParamTypes = methodType.getParameterTypes();

                if (methodType.getReceiverType() != null) {
                    AnnotatedTypeMirror requiredReceiverType = methodType.getReceiverType();
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredReceiverType);
                    printlnAligned(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, "this"));
                }

                for (int i = 0; i < requiredParamTypes.size(); ++i) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                    printlnAligned(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, paramNames.get(i)));
                }
            }

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID) {
                for (LatticeVisitor.Result wellTypedness : results) {
                    AnnotatedTypeMirror returnType = wellTypedness.getTypeFactory().getMethodReturnType(tree);
                    AnnotationMirror anno = returnType.getAnnotationInHierarchy(wellTypedness.getTypeFactory().getTop());

                    if (anno != null && !AnnotationUtils.areSame(
                            anno,
                            wellTypedness.getTypeFactory().getTop())) {
                        PropertyAnnotation pa = wellTypedness.getLattice().getPropertyAnnotation(returnType);
                        PropertyAnnotationType pat = pa.getAnnotationType();

                        if (pat.isTrivial()) {
                            continue;
                        }

                        printlnAligned(new Condition(ConditionType.ASSUMPTION, ConditionLocation.POSTCONDITION, pa, "\\result").toString());
                    }
                }
            }

            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

            for (String clause : getJMLClauseValues(element)) {
                if (isConstructor(tree)) {
                    if (clause.startsWith("assignable")) {
                        clause = clause.replace("this.*", "\\nothing");
                    } else {
                        clause = clause.replace("this", "\\result");
                    }
                }

                printlnAligned(String.format("  @ %s;", clause));
            }

            if (TRANSLATION_RAW) {
                for (String clause : getJMLClauseValuesTranslationOnly(element)) {
                    if (isConstructor(tree)) {
                        if (clause.startsWith("assignable")) {
                            clause = clause.replace("this.*", "\\nothing");
                        } else {
                            clause = clause.replace("this", "\\result");
                        }
                    }

                    printlnAligned(String.format("  @ %s;", clause));
                }
            }

            printlnAligned("  @ diverges true;");
            printlnAligned("  @*/");

            if (printBody) {
                printlnAligned(String.format("public /*@helper@*/ %s %s%s %s(%s) {",
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
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }
    
    protected void printTrampolineOpenJML(JCMethodDecl tree, boolean printBody) {
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

        try {
            AnnotatedExecutableType propertyMethodType = propertyFactory.getAnnotatedType(tree);

            printlnAligned("/*@ public behavior");

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
                        printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, "this")
                                .toStringOr(trampolineBooleanParamName("this", wellTypedness)));
                    }
                }

                for (int i = 0; i < requiredParamTypes.size(); ++i) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                    PropertyAnnotationType pat = pa.getAnnotationType();

                    if (!pat.isTrivial()
                            && !AnnotationUtils.areSame(requiredParamTypes.get(i).getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                        printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.PRECONDITION, pa, paramNames.get(i))
                                .toStringOr(trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
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
                    printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.POSTCONDITION, pa, "this"));
                }

                for (int i = 0; i < requiredParamTypes.size(); ++i) {
                    PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                    printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.POSTCONDITION, pa, paramNames.get(i)));
                }
            }

            if (propertyMethodType.getReturnType().getKind() != TypeKind.VOID) {
                for (LatticeVisitor.Result wellTypedness : results) {
                    AnnotatedTypeMirror returnType = wellTypedness.getTypeFactory().getMethodReturnType(tree);
                    AnnotationMirror anno = returnType.getAnnotationInHierarchy(wellTypedness.getTypeFactory().getTop());

                    if (anno != null && !AnnotationUtils.areSame(
                            anno,
                            wellTypedness.getTypeFactory().getTop())) {
                        PropertyAnnotation pa = wellTypedness.getLattice().getPropertyAnnotation(returnType);
                        PropertyAnnotationType pat = pa.getAnnotationType();

                        if (pat.isTrivial()) {
                            continue;
                        }

                        printlnAligned(new Condition(ConditionType.ASSERTION, ConditionLocation.POSTCONDITION, pa, "\\result").toString());
                    }
                }
            }

            ExecutableElement element = propertyFactory.getAnnotatedType(tree).getElement();

            for (String clause : getJMLClauseValues(element)) {
                if (isConstructor(tree)) {
                    if (clause.startsWith("assignable")) {
                        clause = clause.replace("this.*", "\\nothing");
                    } else {
                        clause = clause.replace("this", "\\result");
                    }
                }

                printlnAligned(String.format("  @ %s;", clause));
            }

            if (TRANSLATION_RAW) {
                for (String clause : getJMLClauseValues(element)) {
                    if (isConstructor(tree)) {
                        if (clause.startsWith("assignable")) {
                            clause = clause.replace("this.*", "\\nothing");
                        } else {
                            clause = clause.replace("this", "\\result");
                        }
                    }

                    printlnAligned(String.format("  @ %s;", clause));
                }
            }

            printlnAligned("  @ diverges true;");
            printlnAligned("  @*/");

            if (printBody) {
                printlnAligned(String.format("public %s %s %s(%s) {",
                        ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                        TypeUtils.unannotatedTypeName(propertyMethodType.getReturnType()),
                        trampolineName(tree.getName()),
                        paramStr));

                indent();
                
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
                            printlnAligned(new Condition(ConditionType.ASSUMPTION, ConditionLocation.ASSERTION, pa, "this")
                                    .toStringOr("!" + trampolineBooleanParamName("this", wellTypedness)));
                        }
                    }

                    for (int i = 0; i < requiredParamTypes.size(); ++i) {
                        PropertyAnnotation pa = lattice.getPropertyAnnotation(requiredParamTypes.get(i));
                        PropertyAnnotationType pat = pa.getAnnotationType();

                        if (!pat.isTrivial()
                                && !AnnotationUtils.areSame(requiredParamTypes.get(i).getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                            printlnAligned(new Condition(ConditionType.ASSUMPTION, ConditionLocation.ASSERTION, pa, paramNames.get(i))
                                    .toStringOr("!" + trampolineBooleanParamName(paramNames.get(i), wellTypedness)));
                        }
                    }
                }

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
                printlnAligned(String.format("public %s %s %s(%s);",
                        ElementUtils.isStatic(propertyMethodType.getElement()) || isConstructor(tree) ? "static" : "",
                        TypeUtils.unannotatedTypeName(propertyMethodType.getReturnType()),
                        trampolineName(tree.getName()),
                        paramStr));
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    protected void printlnAligned(Condition cond) throws IOException {
        PropertyAnnotationType pat = cond.pa.getAnnotationType();

        if (pat.isTrivial()) {
            return;
        }

        printlnAligned(cond.toString());
    }

    protected void printlnAligned(String s) throws IOException {
        align();
        println(s);
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
        		|| TRANSLATION_JML_DIALECT == JMLDialect.OpenJMLDialect
        		? "" : "/*@nullable@*/ ")
                + TypeUtils.unannotatedTypeName(type);
    }

    protected String unannotatedTypeNameLhs(JCTree tree) {
        return TypeUtils.unannotatedTypeName(results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree));
    }

    protected String unannotatedNullableTypeNameLhs(JCTree tree) {
        AnnotatedTypeMirror type = results.get(0).getTypeFactory().getAnnotatedTypeLhs(tree);

        return (type.getKind() == TypeKind.VOID || type.getKind().isPrimitive()
        		|| TRANSLATION_JML_DIALECT == JMLDialect.OpenJMLDialect
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

    protected List<Condition> getConditions(JCReturn tree, String subject, ConditionLocation conditionLocation) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

            if (returnType instanceof AnnotatedExecutableType
                    || AnnotationUtils.areSame(returnType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())
                    || tree.getExpression() == null) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTyped(tree);

            PropertyAnnotation pa = lattice.getPropertyAnnotation(returnType);
            (wt ? wellTyped : malTyped).add(new Condition(wt, conditionLocation, pa, subject));
        }

        return Streams.concat(wellTyped.stream(), malTyped.stream()).collect(Collectors.toList());
    }

    protected List<Condition> getPostconditionsForMethod(JCMethodDecl tree, String subject) {
        List<Condition> postConditions = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror returnType = factory.getMethodReturnType(enclMethod);

            if (returnType instanceof AnnotatedExecutableType
                    || returnType.getKind() == TypeKind.VOID
                    || AnnotationUtils.areSame(returnType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();

            PropertyAnnotation pa = lattice.getPropertyAnnotation(returnType);
            postConditions.add(new Condition(ConditionType.ASSERTION, ConditionLocation.POSTCONDITION, pa, subject));
        }

        return postConditions;
    }

    protected List<Condition> getPostconditionsForConstructor(JCMethodDecl tree, String subject) {
        List<Condition> wellTyped = new ArrayList<>();
        List<Condition> malTyped = new ArrayList<>();

        for (LatticeVisitor.Result wellTypedness : results) {
            LatticeAnnotatedTypeFactory factory = wellTypedness.getTypeFactory();
            AnnotatedTypeMirror receiverType = factory.getMethodReturnType(enclMethod);

            if (AnnotationUtils.areSame(receiverType.getAnnotationInHierarchy(factory.getTop()), factory.getTop())) {
                continue;
            }

            Lattice lattice = wellTypedness.getLattice();
            boolean wt = wellTypedness.isWellTypedConstructor(tree);

            PropertyAnnotation pa = lattice.getPropertyAnnotation(receiverType);
            (wt ? wellTyped : malTyped).add(new Condition(wt, ConditionLocation.POSTCONDITION, pa, subject));
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
    
    public enum JMLDialect {
    	KeYJMLDialect, OpenJMLDialect
    };

    public enum ConditionLocation {
        ASSERTION, PRECONDITION, POSTCONDITION;
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
                    sb.append("  @ requires ");
                    break;
                case ASSUMPTION:
                    sb.append("  @ requires_free ");
                    break;
                default:
                    throw new IllegalStateException();
                }
                break;
            case POSTCONDITION:
                switch(conditionType) {
                case ASSERTION:
                    sb.append("  @ ensures ");
                    break;
                case ASSUMPTION:
                    sb.append(TRANSLATION_RAW ? "  @ ensures " : "  @ ensures_free ");
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
}
