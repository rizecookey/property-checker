/* This file is an exact duplicate of {@link com.sun.tools.javac.tree.Pretty}
 * put here to be able to access package-private members.
 */

/*
 * Copyright (c) 1999, 2018, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.  Oracle designates this
 * particular file as subject to the "Classpath" exception as provided
 * by Oracle in the LICENSE file that accompanied this code.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 */

package edu.kit.kastel.property.printer;

import com.sun.source.tree.MemberReferenceTree.ReferenceMode;
import com.sun.source.tree.ModuleTree.ModuleKind;
import com.sun.tools.javac.code.BoundKind;
import com.sun.tools.javac.code.Symbol;
import com.sun.tools.javac.tree.*;
import com.sun.tools.javac.tree.JCTree.JCCase;
import com.sun.tools.javac.tree.JCTree.Tag;
import com.sun.tools.javac.util.Convert;
import com.sun.tools.javac.util.List;
import com.sun.tools.javac.util.Name;

import java.io.IOException;
import java.io.StringWriter;
import java.io.UncheckedIOException;
import java.io.Writer;
import java.util.Iterator;
import java.util.stream.Collectors;

/** Duplicate of {@link com.sun.tools.javac.tree.Pretty} to be able to access package-private members.
 */
@SuppressWarnings("all")
public class PrettyPrinter extends JCTree.Visitor {
    private final boolean sourceOutput;
    Writer out;
    public int width = 4;
    int lmargin = 0;
    Name enclClassName;
    DocCommentTable docComments = null;
    private static final String trimSequence = "[...]";
    private static final int PREFERRED_LENGTH = 20;
    String lineSep = System.getProperty("line.separator");
    int prec;

    public PrettyPrinter(Writer out, boolean sourceOutput) {
        this.out = out;
        this.sourceOutput = sourceOutput;
    }

    void align() throws IOException {
        for(int i = 0; i < this.lmargin; ++i) {
            this.out.write(" ");
        }

    }

    void indent() {
        this.lmargin += this.width;
    }

    void undent() {
        this.lmargin -= this.width;
    }

    void open(int contextPrec, int ownPrec) throws IOException {
        if (ownPrec < contextPrec) {
            this.out.write("(");
        }

    }

    void close(int contextPrec, int ownPrec) throws IOException {
        if (ownPrec < contextPrec) {
            this.out.write(")");
        }

    }

    public void print(Object s) throws IOException {
        this.out.write(Convert.escapeUnicode(s.toString()));
    }

    private void print(char c) throws IOException {
        this.out.write(c);
    }

    public void println() throws IOException {
        this.out.write(this.lineSep);
    }

    public static String toSimpleString(JCTree tree) {
        return toSimpleString(tree, 20);
    }

    public static String toSimpleString(JCTree tree, int maxLength) {
        StringWriter s = new StringWriter();

        try {
            (new Pretty(s, false)).printExpr(tree);
        } catch (IOException var6) {
            throw new AssertionError(var6);
        }

        String res = s.toString().trim().replaceAll("\\s+", " ").replaceAll("/\\*missing\\*/", "");
        if (res.length() < maxLength) {
            return res;
        } else {
            int head = (maxLength - "[...]".length()) * 2 / 3;
            int tail = maxLength - "[...]".length() - head;
            return res.substring(0, head) + "[...]" + res.substring(res.length() - tail);
        }
    }

    public void printExpr(JCTree tree, int prec) throws IOException {
        int prevPrec = this.prec;

        try {
            this.prec = prec;
            if (tree == null) {
                this.print("/*missing*/");
            } else {
                tree.accept(this);
            }
        } catch (UncheckedIOException var8) {
            throw var8.getCause();
        } finally {
            this.prec = prevPrec;
        }

    }

    public void printExpr(JCTree tree) throws IOException {
        this.printExpr(tree, 0);
    }

    public void printStat(JCTree tree) throws IOException {
        this.printExpr(tree, -1);
    }

    public <T extends JCTree> void printExprs(List<T> trees, String sep) throws IOException {
        if (trees.nonEmpty()) {
            this.printExpr((JCTree)trees.head);

            for(List<T> l = trees.tail; l.nonEmpty(); l = l.tail) {
                this.print(sep);
                this.printExpr((JCTree)l.head);
            }
        }

    }

    public <T extends JCTree> void printExprs(List<T> trees) throws IOException {
        this.printExprs(trees, ", ");
    }

    public void printPattern(JCTree tree) throws IOException {
        this.printExpr(tree);
    }

    public void printStats(List<? extends JCTree> trees) throws IOException {
        for(List<? extends JCTree> l = trees; l.nonEmpty(); l = l.tail) {
            this.align();
            this.printStat((JCTree)l.head);
            this.println();
        }

    }

    public void printFlags(long flags) throws IOException {
        if ((flags & 4096L) != 0L) {
            this.print("/*synthetic*/ ");
        }

        this.print(TreeInfo.flagNames(flags));
        if ((flags & -4611677222334361601L) != 0L) {
            this.print(' ');
        }

        if ((flags & 8192L) != 0L) {
            this.print('@');
        }

    }

    public void printAnnotations(List<JCTree.JCAnnotation> trees) throws IOException {
        for(List<JCTree.JCAnnotation> l = trees; l.nonEmpty(); l = l.tail) {
            this.printStat((JCTree)l.head);
            this.println();
            this.align();
        }

    }

    public void printTypeAnnotations(List<JCTree.JCAnnotation> trees) throws IOException {
        for(List<JCTree.JCAnnotation> l = trees; l.nonEmpty(); l = l.tail) {
            this.printExpr((JCTree)l.head);
            this.print(' ');
        }

    }

    public void printDocComment(JCTree tree) throws IOException {
        if (this.docComments != null) {
            String dc = this.docComments.getCommentText(tree);
            if (dc != null) {
                this.print("/**");
                this.println();
                int pos = 0;

                for(int endpos = lineEndPos(dc, pos); pos < dc.length(); endpos = lineEndPos(dc, pos)) {
                    this.align();
                    this.print(" *");
                    if (pos < dc.length() && dc.charAt(pos) > ' ') {
                        this.print(' ');
                    }

                    this.print(dc.substring(pos, endpos));
                    this.println();
                    pos = endpos + 1;
                }

                this.align();
                this.print(" */");
                this.println();
                this.align();
            }
        }

    }

    static int lineEndPos(String s, int start) {
        int pos = s.indexOf(10, start);
        if (pos < 0) {
            pos = s.length();
        }

        return pos;
    }

    public void printTypeParameters(List<JCTree.JCTypeParameter> trees) throws IOException {
        if (trees.nonEmpty()) {
            this.print('<');
            this.printExprs(trees);
            this.print('>');
        }

    }

    public void printBlock(List<? extends JCTree> stats) throws IOException {
        this.print('{');
        this.println();
        this.indent();
        this.printStats(stats);
        this.undent();
        this.align();
        this.print('}');
    }

    public void printEnumBody(List<JCTree> stats) throws IOException {
        this.print('{');
        this.println();
        this.indent();
        boolean first = true;

        List l;
        for(l = stats; l.nonEmpty(); l = l.tail) {
            if (this.isEnumerator((JCTree)l.head)) {
                if (!first) {
                    this.print(',');
                    this.println();
                }

                this.align();
                this.printStat((JCTree)l.head);
                first = false;
            }
        }

        this.print(';');
        this.println();

        for(l = stats; l.nonEmpty(); l = l.tail) {
            if (!this.isEnumerator((JCTree)l.head)) {
                this.align();
                this.printStat((JCTree)l.head);
                this.println();
            }
        }

        this.undent();
        this.align();
        this.print('}');
    }

    boolean isEnumerator(JCTree t) {
        return t.hasTag(Tag.VARDEF) && (((JCTree.JCVariableDecl)t).mods.flags & 16384L) != 0L;
    }

    public void printUnit(JCTree.JCCompilationUnit tree, JCTree.JCClassDecl cdef) throws IOException {
        this.docComments = tree.docComments;
        this.printDocComment(tree);
        boolean firstImport = true;

        for(List<JCTree> l = tree.defs; l.nonEmpty() && (cdef == null || ((JCTree)l.head).hasTag(Tag.IMPORT) || ((JCTree)l.head).hasTag(Tag.PACKAGEDEF)); l = l.tail) {
            if (((JCTree)l.head).hasTag(Tag.IMPORT)) {
                JCTree.JCImport imp = (JCTree.JCImport)l.head;
                Name name = TreeInfo.name(imp.qualid);
                if (name == name.table.names.asterisk || cdef == null || this.isUsed(TreeInfo.symbol(imp.qualid), cdef)) {
                    if (firstImport) {
                        firstImport = false;
                        this.println();
                    }

                    this.printStat(imp);
                }
            } else {
                this.printStat((JCTree)l.head);
            }
        }

        if (cdef != null) {
            this.printStat(cdef);
            this.println();
        }

    }

    boolean isUsed(final Symbol t, JCTree cdef) {
        class UsedVisitor extends TreeScanner {
            boolean result = false;

            UsedVisitor(final PrettyPrinter this$0) {
            }

            public void scan(JCTree tree) {
                if (tree != null && !this.result) {
                    tree.accept(this);
                }

            }

            public void visitIdent(JCTree.JCIdent tree) {
                if (tree.sym == t) {
                    this.result = true;
                }

            }
        }

        UsedVisitor v = new UsedVisitor(this);
        v.scan(cdef);
        return v.result;
    }

    public void visitTopLevel(JCTree.JCCompilationUnit tree) {
        try {
            this.printUnit(tree, (JCTree.JCClassDecl)null);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitPackageDef(JCTree.JCPackageDecl tree) {
        try {
            this.printDocComment(tree);
            this.printAnnotations(tree.annotations);
            if (tree.pid != null) {
                this.print("package ");
                this.printExpr(tree.pid);
                this.print(';');
                this.println();
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitModuleDef(JCTree.JCModuleDecl tree) {
        try {
            this.printDocComment(tree);
            this.printAnnotations(tree.mods.annotations);
            if (tree.getModuleType() == ModuleKind.OPEN) {
                this.print("open ");
            }

            this.print("module ");
            this.printExpr(tree.qualId);
            if (tree.directives == null) {
                this.print(';');
            } else {
                this.print(' ');
                this.printBlock(tree.directives);
            }

            this.println();
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitExports(JCTree.JCExports tree) {
        try {
            this.print("exports ");
            this.printExpr(tree.qualid);
            if (tree.moduleNames != null) {
                this.print(" to ");
                this.printExprs(tree.moduleNames);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitOpens(JCTree.JCOpens tree) {
        try {
            this.print("opens ");
            this.printExpr(tree.qualid);
            if (tree.moduleNames != null) {
                this.print(" to ");
                this.printExprs(tree.moduleNames);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitProvides(JCTree.JCProvides tree) {
        try {
            this.print("provides ");
            this.printExpr(tree.serviceName);
            this.print(" with ");
            this.printExprs(tree.implNames);
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitRequires(JCTree.JCRequires tree) {
        try {
            this.print("requires ");
            if (tree.isStaticPhase) {
                this.print("static ");
            }

            if (tree.isTransitive) {
                this.print("transitive ");
            }

            this.printExpr(tree.moduleName);
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitUses(JCTree.JCUses tree) {
        try {
            this.print("uses ");
            this.printExpr(tree.qualid);
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitImport(JCTree.JCImport tree) {
        try {
            this.print("import ");
            if (tree.staticImport) {
                this.print("static ");
            }

            this.printExpr(tree.qualid);
            this.print(';');
            this.println();
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitClassDef(JCTree.JCClassDecl tree) {
        try {
            this.println();
            this.align();
            this.printDocComment(tree);
            this.printAnnotations(tree.mods.annotations);
            this.printFlags(tree.mods.flags & -513L);
            Name enclClassNamePrev = this.enclClassName;
            this.enclClassName = tree.name;
            if ((tree.mods.flags & 512L) != 0L) {
                this.print("interface ");
                this.print(tree.name);
                this.printTypeParameters(tree.typarams);
                if (tree.implementing.nonEmpty()) {
                    this.print(" extends ");
                    this.printExprs(tree.implementing);
                }

                if (tree.permitting.nonEmpty()) {
                    this.print(" permits ");
                    this.printExprs(tree.permitting);
                }
            } else {
                if ((tree.mods.flags & 16384L) != 0L) {
                    this.print("enum ");
                } else {
                    this.print("class ");
                }

                this.print(tree.name);
                this.printTypeParameters(tree.typarams);
                if (tree.extending != null) {
                    this.print(" extends ");
                    this.printExpr(tree.extending);
                }

                if (tree.implementing.nonEmpty()) {
                    this.print(" implements ");
                    this.printExprs(tree.implementing);
                }

                if (tree.permitting.nonEmpty()) {
                    this.print(" permits ");
                    this.printExprs(tree.permitting);
                }
            }

            this.print(' ');
            if ((tree.mods.flags & 16384L) != 0L) {
                this.printEnumBody(tree.defs);
            } else {
                this.printBlock(tree.defs);
            }

            this.enclClassName = enclClassNamePrev;
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitMethodDef(JCTree.JCMethodDecl tree) {
        try {
            if (tree.name != tree.name.table.names.init || this.enclClassName != null || !this.sourceOutput) {
                this.println();
                this.align();
                this.printDocComment(tree);
                this.printExpr(tree.mods);
                this.printTypeParameters(tree.typarams);
                if (tree.name == tree.name.table.names.init) {
                    this.print(this.enclClassName != null ? this.enclClassName : tree.name);
                } else {
                    this.printExpr(tree.restype);
                    this.print(' ');
                    this.print(tree.name);
                }

                this.print('(');
                if (tree.recvparam != null) {
                    this.printExpr(tree.recvparam);
                    if (tree.params.size() > 0) {
                        this.print(", ");
                    }
                }

                this.printExprs(tree.params);
                this.print(')');
                if (tree.thrown.nonEmpty()) {
                    this.print(" throws ");
                    this.printExprs(tree.thrown);
                }

                if (tree.defaultValue != null) {
                    this.print(" default ");
                    this.printExpr(tree.defaultValue);
                }

                if (tree.body != null) {
                    this.print(' ');
                    this.printStat(tree.body);
                } else {
                    this.print(';');
                }

            }
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitVarDef(JCTree.JCVariableDecl tree) {
        try {
            if (this.docComments != null && this.docComments.hasComment(tree)) {
                this.println();
                this.align();
            }

            this.printDocComment(tree);
            if ((tree.mods.flags & 16384L) != 0L) {
                this.print("/*public static final*/ ");
                this.print(tree.name);
                if (tree.init != null) {
                    if (tree.init.hasTag(Tag.NEWCLASS)) {
                        JCTree.JCNewClass init = (JCTree.JCNewClass)tree.init;
                        if (this.sourceOutput) {
                            this.print(" /*enum*/ ");
                            if (init.args != null && init.args.nonEmpty()) {
                                this.print('(');
                                this.print(init.args);
                                this.print(')');
                            }

                            if (init.def != null && init.def.defs != null) {
                                this.print(' ');
                                this.printBlock(init.def.defs);
                            }

                            return;
                        }

                        this.print(" /* = ");
                        this.print("new ");
                        if (init.def != null && init.def.mods.annotations.nonEmpty()) {
                            this.printTypeAnnotations(init.def.mods.annotations);
                        }

                        this.printExpr(init.clazz);
                        this.print('(');
                        this.printExprs(init.args);
                        this.print(')');
                        this.print(" */");
                        this.print(" /*enum*/ ");
                        if (init.args != null && init.args.nonEmpty()) {
                            this.print('(');
                            this.printExprs(init.args);
                            this.print(')');
                        }

                        if (init.def != null && init.def.defs != null) {
                            this.print(' ');
                            this.printBlock(init.def.defs);
                        }

                        return;
                    }

                    this.print(" /* = ");
                    this.printExpr(tree.init);
                    this.print(" */");
                }
            } else {
                this.printExpr(tree.mods);
                if ((tree.mods.flags & 17179869184L) != 0L) {
                    JCTree vartype = tree.vartype;
                    List<JCTree.JCAnnotation> tas = null;
                    if (vartype instanceof JCTree.JCAnnotatedType) {
                        JCTree.JCAnnotatedType annotatedType = (JCTree.JCAnnotatedType)vartype;
                        tas = annotatedType.annotations;
                        vartype = annotatedType.underlyingType;
                    }

                    this.printExpr(((JCTree.JCArrayTypeTree)vartype).elemtype);
                    if (tas != null) {
                        this.print(' ');
                        this.printTypeAnnotations(tas);
                    }

                    this.print("... ");
                    this.print(tree.name);
                } else {
                    this.printExpr(tree.vartype);
                    this.print(' ');
                    if (tree.name.isEmpty()) {
                        this.print('_');
                    } else {
                        this.print(tree.name);
                    }
                }

                if (tree.init != null) {
                    this.print(" = ");
                    this.printExpr(tree.init);
                }

                if (this.prec == -1) {
                    this.print(';');
                }
            }

        } catch (IOException var5) {
            throw new UncheckedIOException(var5);
        }
    }

    public void visitSkip(JCTree.JCSkip tree) {
        try {
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitBlock(JCTree.JCBlock tree) {
        try {
            this.printFlags(tree.flags);
            this.printBlock(tree.stats);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitDoLoop(JCTree.JCDoWhileLoop tree) {
        try {
            this.print("do ");
            this.printStat(tree.body);
            this.align();
            this.print(" while ");
            if (tree.cond.hasTag(Tag.PARENS)) {
                this.printExpr(tree.cond);
            } else {
                this.print('(');
                this.printExpr(tree.cond);
                this.print(')');
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitWhileLoop(JCTree.JCWhileLoop tree) {
        try {
            this.print("while ");
            if (tree.cond.hasTag(Tag.PARENS)) {
                this.printExpr(tree.cond);
            } else {
                this.print('(');
                this.printExpr(tree.cond);
                this.print(')');
            }

            this.print(' ');
            this.printStat(tree.body);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitForLoop(JCTree.JCForLoop tree) {
        try {
            this.print("for (");
            if (tree.init.nonEmpty()) {
                if (((JCTree.JCStatement)tree.init.head).hasTag(Tag.VARDEF)) {
                    this.printExpr((JCTree)tree.init.head);

                    for(List<JCTree.JCStatement> l = tree.init.tail; l.nonEmpty(); l = l.tail) {
                        JCTree.JCVariableDecl vdef = (JCTree.JCVariableDecl)l.head;
                        this.print(", ");
                        this.print(vdef.name);
                        if (vdef.init != null) {
                            this.print(" = ");
                            this.printExpr(vdef.init);
                        }
                    }
                } else {
                    this.printExprs(tree.init);
                }
            }

            this.print("; ");
            if (tree.cond != null) {
                this.printExpr(tree.cond);
            }

            this.print("; ");
            this.printExprs(tree.step);
            this.print(") ");
            this.printStat(tree.body);
        } catch (IOException var4) {
            throw new UncheckedIOException(var4);
        }
    }

    public void visitForeachLoop(JCTree.JCEnhancedForLoop tree) {
        try {
            this.print("for (");
            this.printExpr(tree.var);
            this.print(" : ");
            this.printExpr(tree.expr);
            this.print(") ");
            this.printStat(tree.body);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitLabelled(JCTree.JCLabeledStatement tree) {
        try {
            this.print(tree.label);
            this.print(": ");
            this.printStat(tree.body);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitSwitch(JCTree.JCSwitch tree) {
        try {
            this.print("switch ");
            if (tree.selector.hasTag(Tag.PARENS)) {
                this.printExpr(tree.selector);
            } else {
                this.print('(');
                this.printExpr(tree.selector);
                this.print(')');
            }

            this.print(" {");
            this.println();
            this.printStats(tree.cases);
            this.align();
            this.print('}');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitCase(JCTree.JCCase tree) {
        try {
            if (tree.labels.size() == 1 && ((JCTree.JCCaseLabel)tree.labels.get(0)).hasTag(Tag.DEFAULTCASELABEL)) {
                this.print("default");
            } else {
                this.print("case ");
                this.printExprs(tree.labels);
            }

            if (tree.guard != null) {
                this.print(" when ");
                this.print(tree.guard);
            }

            if (tree.caseKind == JCCase.STATEMENT) {
                this.print(':');
                this.println();
                this.indent();
                this.printStats(tree.stats);
                this.undent();
                this.align();
            } else {
                this.print(" -> ");
                if (tree.stats.size() == 1) {
                    this.printStat((JCTree)tree.stats.head);
                } else {
                    this.printBlock(tree.stats);
                }
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitDefaultCaseLabel(JCTree.JCDefaultCaseLabel that) {
        try {
            this.print("default");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitConstantCaseLabel(JCTree.JCConstantCaseLabel tree) {
        try {
            this.print(tree.expr);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitPatternCaseLabel(JCTree.JCPatternCaseLabel tree) {
        try {
            this.print(tree.pat);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitSwitchExpression(JCTree.JCSwitchExpression tree) {
        try {
            this.print("switch ");
            if (tree.selector.hasTag(Tag.PARENS)) {
                this.printExpr(tree.selector);
            } else {
                this.print('(');
                this.printExpr(tree.selector);
                this.print(')');
            }

            this.print(" {");
            this.println();
            this.printStats(tree.cases);
            this.align();
            this.print('}');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitBindingPattern(JCTree.JCBindingPattern patt) {
        try {
            this.printExpr(patt.var);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitAnyPattern(JCTree.JCAnyPattern patt) {
        try {
            this.print('_');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitRecordPattern(JCTree.JCRecordPattern tree) {
        try {
            this.printExpr(tree.deconstructor);
            this.print('(');
            this.printExprs(tree.nested);
            this.print(')');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitSynchronized(JCTree.JCSynchronized tree) {
        try {
            this.print("synchronized ");
            if (tree.lock.hasTag(Tag.PARENS)) {
                this.printExpr(tree.lock);
            } else {
                this.print('(');
                this.printExpr(tree.lock);
                this.print(')');
            }

            this.print(' ');
            this.printStat(tree.body);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTry(JCTree.JCTry tree) {
        try {
            this.print("try ");
            if (tree.resources.nonEmpty()) {
                this.print('(');
                boolean first = true;

                for(Iterator var3 = tree.resources.iterator(); var3.hasNext(); first = false) {
                    JCTree var = (JCTree)var3.next();
                    if (!first) {
                        this.println();
                        this.indent();
                    }

                    this.printStat(var);
                }

                this.print(") ");
            }

            this.printStat(tree.body);

            for(List<JCTree.JCCatch> l = tree.catchers; l.nonEmpty(); l = l.tail) {
                this.printStat((JCTree)l.head);
            }

            if (tree.finalizer != null) {
                this.print(" finally ");
                this.printStat(tree.finalizer);
            }

        } catch (IOException var5) {
            throw new UncheckedIOException(var5);
        }
    }

    public void visitCatch(JCTree.JCCatch tree) {
        try {
            this.print(" catch (");
            this.printExpr(tree.param);
            this.print(") ");
            this.printStat(tree.body);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitConditional(JCTree.JCConditional tree) {
        try {
            this.open(this.prec, 3);
            this.printExpr(tree.cond, 4);
            this.print(" ? ");
            this.printExpr(tree.truepart);
            this.print(" : ");
            this.printExpr(tree.falsepart, 3);
            this.close(this.prec, 3);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitIf(JCTree.JCIf tree) {
        try {
            this.print("if ");
            if (tree.cond.hasTag(Tag.PARENS)) {
                this.printExpr(tree.cond);
            } else {
                this.print('(');
                this.printExpr(tree.cond);
                this.print(')');
            }

            this.print(' ');
            this.printStat(tree.thenpart);
            if (tree.elsepart != null) {
                this.print(" else ");
                this.printStat(tree.elsepart);
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitExec(JCTree.JCExpressionStatement tree) {
        try {
            this.printExpr(tree.expr);
            if (this.prec == -1) {
                this.print(';');
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitBreak(JCTree.JCBreak tree) {
        try {
            this.print("break");
            if (tree.label != null) {
                this.print(' ');
                this.print(tree.label);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitYield(JCTree.JCYield tree) {
        try {
            this.print("yield");
            this.print(' ');
            this.printExpr(tree.value);
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitContinue(JCTree.JCContinue tree) {
        try {
            this.print("continue");
            if (tree.label != null) {
                this.print(' ');
                this.print(tree.label);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitReturn(JCTree.JCReturn tree) {
        try {
            this.print("return");
            if (tree.expr != null) {
                this.print(' ');
                this.printExpr(tree.expr);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitThrow(JCTree.JCThrow tree) {
        try {
            this.print("throw ");
            this.printExpr(tree.expr);
            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitAssert(JCTree.JCAssert tree) {
        try {
            this.print("assert ");
            this.printExpr(tree.cond);
            if (tree.detail != null) {
                this.print(" : ");
                this.printExpr(tree.detail);
            }

            this.print(';');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitApply(JCTree.JCMethodInvocation tree) {
        try {
            if (!tree.typeargs.isEmpty()) {
                if (tree.meth.hasTag(Tag.SELECT)) {
                    JCTree.JCFieldAccess left = (JCTree.JCFieldAccess)tree.meth;
                    this.printExpr(left.selected);
                    this.print(".<");
                    this.printExprs(tree.typeargs);
                    this.print('>');
                    this.print(left.name);
                } else {
                    this.print('<');
                    this.printExprs(tree.typeargs);
                    this.print('>');
                    this.printExpr(tree.meth);
                }
            } else {
                this.printExpr(tree.meth);
            }

            this.print('(');
            this.printExprs(tree.args);
            this.print(')');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitNewClass(JCTree.JCNewClass tree) {
        try {
            if (tree.encl != null) {
                this.printExpr(tree.encl);
                this.print('.');
            }

            this.print("new ");
            if (!tree.typeargs.isEmpty()) {
                this.print('<');
                this.printExprs(tree.typeargs);
                this.print('>');
            }

            if (tree.def != null && tree.def.mods.annotations.nonEmpty()) {
                this.printTypeAnnotations(tree.def.mods.annotations);
            }

            this.printExpr(tree.clazz);
            this.print('(');
            this.printExprs(tree.args);
            this.print(')');
            if (tree.def != null) {
                Name enclClassNamePrev = this.enclClassName;
                this.enclClassName = tree.def.name != null ? tree.def.name : (tree.type != null && tree.type.tsym.name != tree.type.tsym.name.table.names.empty ? tree.type.tsym.name : null);
                if ((tree.def.mods.flags & 16384L) != 0L) {
                    this.print("/*enum*/");
                }

                this.printBlock(tree.def.defs);
                this.enclClassName = enclClassNamePrev;
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitNewArray(JCTree.JCNewArray tree) {
        try {
            if (tree.elemtype != null) {
                this.print("new ");
                JCTree elem = tree.elemtype;
                this.printBaseElementType(elem);
                if (!tree.annotations.isEmpty()) {
                    this.print(' ');
                    this.printTypeAnnotations(tree.annotations);
                }

                if (tree.elems != null) {
                    this.print("[]");
                }

                int i = 0;
                List<List<JCTree.JCAnnotation>> da = tree.dimAnnotations;

                for(List<JCTree.JCExpression> l = tree.dims; l.nonEmpty(); l = l.tail) {
                    if (da.size() > i && !((List)da.get(i)).isEmpty()) {
                        this.print(' ');
                        this.printTypeAnnotations((List)da.get(i));
                    }

                    this.print('[');
                    ++i;
                    this.printExpr((JCTree)l.head);
                    this.print(']');
                }

                this.printBrackets(elem);
            }

            if (tree.elems != null) {
                this.print('{');
                this.printExprs(tree.elems);
                this.print('}');
            }

        } catch (IOException var6) {
            throw new UncheckedIOException(var6);
        }
    }

    public void visitLambda(JCTree.JCLambda tree) {
        try {
            this.print('(');
            if (tree.paramKind == JCTree.JCLambda.ParameterKind.EXPLICIT) {
                this.printExprs(tree.params);
            } else {
                String sep = "";

                for(Iterator var3 = tree.params.iterator(); var3.hasNext(); sep = ",") {
                    JCTree.JCVariableDecl param = (JCTree.JCVariableDecl)var3.next();
                    this.print(sep);
                    this.print(param.name);
                }
            }

            this.print(")->");
            this.printExpr(tree.body);
        } catch (IOException var5) {
            throw new UncheckedIOException(var5);
        }
    }

    public void visitParens(JCTree.JCParens tree) {
        try {
            this.print('(');
            this.printExpr(tree.expr);
            this.print(')');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitAssign(JCTree.JCAssign tree) {
        try {
            this.open(this.prec, 1);
            this.printExpr(tree.lhs, 2);
            this.print(" = ");
            this.printExpr(tree.rhs, 1);
            this.close(this.prec, 1);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public String operatorName(JCTree.Tag tag) {
        switch (tag) {
        case POS:
            return "+";
        case NEG:
            return "-";
        case NOT:
            return "!";
        case COMPL:
            return "~";
        case PREINC:
            return "++";
        case PREDEC:
            return "--";
        case POSTINC:
            return "++";
        case POSTDEC:
            return "--";
        case NULLCHK:
            return "<*nullchk*>";
        case OR:
            return "||";
        case AND:
            return "&&";
        case EQ:
            return "==";
        case NE:
            return "!=";
        case LT:
            return "<";
        case GT:
            return ">";
        case LE:
            return "<=";
        case GE:
            return ">=";
        case BITOR:
            return "|";
        case BITXOR:
            return "^";
        case BITAND:
            return "&";
        case SL:
            return "<<";
        case SR:
            return ">>";
        case USR:
            return ">>>";
        case PLUS:
            return "+";
        case MINUS:
            return "-";
        case MUL:
            return "*";
        case DIV:
            return "/";
        case MOD:
            return "%";
        default:
            throw new Error();
        }
    }

    public void visitAssignop(JCTree.JCAssignOp tree) {
        try {
            this.open(this.prec, 2);
            this.printExpr(tree.lhs, 3);
            this.print(' ');
            this.print(this.operatorName(tree.getTag().noAssignOp()));
            this.print("= ");
            this.printExpr(tree.rhs, 2);
            this.close(this.prec, 2);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitUnary(JCTree.JCUnary tree) {
        try {
            int ownprec = TreeInfo.opPrec(tree.getTag());
            String opname = this.operatorName(tree.getTag());
            this.open(this.prec, ownprec);
            if (!tree.getTag().isPostUnaryOp()) {
                this.print(opname);
                this.printExpr(tree.arg, ownprec);
            } else {
                this.printExpr(tree.arg, ownprec);
                this.print(opname);
            }

            this.close(this.prec, ownprec);
        } catch (IOException var4) {
            throw new UncheckedIOException(var4);
        }
    }

    public void visitBinary(JCTree.JCBinary tree) {
        try {
            int ownprec = TreeInfo.opPrec(tree.getTag());
            String opname = this.operatorName(tree.getTag());
            this.open(this.prec, ownprec);
            this.printExpr(tree.lhs, ownprec);
            this.print(' ');
            this.print(opname);
            this.print(' ');
            this.printExpr(tree.rhs, ownprec + 1);
            this.close(this.prec, ownprec);
        } catch (IOException var4) {
            throw new UncheckedIOException(var4);
        }
    }

    public void visitTypeCast(JCTree.JCTypeCast tree) {
        try {
            this.open(this.prec, 14);
            this.print('(');
            this.printExpr(tree.clazz);
            this.print(')');
            this.printExpr(tree.expr, 14);
            this.close(this.prec, 14);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeTest(JCTree.JCInstanceOf tree) {
        try {
            this.open(this.prec, 10);
            this.printExpr(tree.expr, 10);
            this.print(" instanceof ");
            if (tree.pattern instanceof JCTree.JCPattern) {
                this.printPattern(tree.pattern);
            } else {
                this.printExpr(tree.getType(), 11);
            }

            this.close(this.prec, 10);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitIndexed(JCTree.JCArrayAccess tree) {
        try {
            this.printExpr(tree.indexed, 15);
            this.print('[');
            this.printExpr(tree.index);
            this.print(']');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitSelect(JCTree.JCFieldAccess tree) {
        try {
            this.printExpr(tree.selected, 15);
            this.print('.');
            this.print(tree.name);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitReference(JCTree.JCMemberReference tree) {
        try {
            this.printExpr(tree.expr);
            this.print("::");
            if (tree.typeargs != null) {
                this.print('<');
                this.printExprs(tree.typeargs);
                this.print('>');
            }

            this.print(tree.getMode() == ReferenceMode.INVOKE ? tree.name : "new");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitIdent(JCTree.JCIdent tree) {
        try {
            this.print(tree.name);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitLiteral(JCTree.JCLiteral tree) {
        try {
            switch (tree.typetag) {
            case INT:
                this.print(tree.value.toString());
                break;
            case LONG:
                this.print(tree.value);
                this.print('L');
                break;
            case FLOAT:
                this.print(tree.value);
                this.print('F');
                break;
            case DOUBLE:
                this.print(tree.value.toString());
                break;
            case CHAR:
                this.print('\'');
                this.print(Convert.quote(String.valueOf((char)((Number)tree.value).intValue())));
                this.print('\'');
                break;
            case BOOLEAN:
                this.print(((Number)tree.value).intValue() == 1 ? "true" : "false");
                break;
            case BOT:
                this.print("null");
                break;
            default:
                this.print('"');
                this.print(Convert.quote(tree.value.toString()));
                this.print('"');
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitStringTemplate(JCTree.JCStringTemplate tree) {
        try {
            JCTree.JCExpression processor = tree.processor;
            this.print("[");
            if (processor != null) {
                this.printExpr(processor);
            }

            this.print("]");
            this.print("\"" + (String)tree.fragments.stream().collect(Collectors.joining("\\{}")) + "\"");
            this.print("(");
            this.printExprs(tree.expressions);
            this.print(")");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeIdent(JCTree.JCPrimitiveTypeTree tree) {
        try {
            switch (tree.typetag) {
            case INT:
                this.print("int");
                break;
            case LONG:
                this.print("long");
                break;
            case FLOAT:
                this.print("float");
                break;
            case DOUBLE:
                this.print("double");
                break;
            case CHAR:
                this.print("char");
                break;
            case BOOLEAN:
                this.print("boolean");
                break;
            case BOT:
            default:
                this.print("error");
                break;
            case BYTE:
                this.print("byte");
                break;
            case SHORT:
                this.print("short");
                break;
            case VOID:
                this.print("void");
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeArray(JCTree.JCArrayTypeTree tree) {
        try {
            this.printBaseElementType(tree);
            this.printBrackets(tree);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    private void printBaseElementType(JCTree tree) throws IOException {
        this.printExpr(TreeInfo.innermostType(tree, false));
    }

    private void printBrackets(JCTree tree) throws IOException {
        JCTree elem = tree;

        while(true) {
            if (((JCTree)elem).hasTag(Tag.ANNOTATED_TYPE)) {
                JCTree.JCAnnotatedType atype = (JCTree.JCAnnotatedType)elem;
                elem = atype.underlyingType;
                if (((JCTree)elem).hasTag(Tag.TYPEARRAY)) {
                    this.print(' ');
                    this.printTypeAnnotations(atype.annotations);
                }
            }

            if (!((JCTree)elem).hasTag(Tag.TYPEARRAY)) {
                return;
            }

            this.print("[]");
            elem = ((JCTree.JCArrayTypeTree)elem).elemtype;
        }
    }

    public void visitTypeApply(JCTree.JCTypeApply tree) {
        try {
            this.printExpr(tree.clazz);
            this.print('<');
            this.printExprs(tree.arguments);
            this.print('>');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeUnion(JCTree.JCTypeUnion tree) {
        try {
            this.printExprs(tree.alternatives, " | ");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeIntersection(JCTree.JCTypeIntersection tree) {
        try {
            this.printExprs(tree.bounds, " & ");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeParameter(JCTree.JCTypeParameter tree) {
        try {
            if (tree.annotations.nonEmpty()) {
                this.printTypeAnnotations(tree.annotations);
            }

            this.print(tree.name);
            if (tree.bounds.nonEmpty()) {
                this.print(" extends ");
                this.printExprs(tree.bounds, " & ");
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitWildcard(JCTree.JCWildcard tree) {
        try {
            this.print(tree.kind);
            if (tree.kind.kind != BoundKind.UNBOUND) {
                this.printExpr(tree.inner);
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTypeBoundKind(JCTree.TypeBoundKind tree) {
        try {
            this.print(String.valueOf(tree.kind));
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitErroneous(JCTree.JCErroneous tree) {
        try {
            this.print("(ERROR)");
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitLetExpr(JCTree.LetExpr tree) {
        try {
            this.print("(let ");
            this.print(tree.defs);
            this.print(" in ");
            this.print(tree.expr);
            this.print(')');
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitModifiers(JCTree.JCModifiers mods) {
        try {
            this.printAnnotations(mods.annotations);
            this.printFlags(mods.flags);
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitAnnotation(JCTree.JCAnnotation tree) {
        try {
            this.print('@');
            this.printExpr(tree.annotationType);
            if (!tree.args.isEmpty()) {
                this.print('(');
                this.printExprs(tree.args);
                this.print(')');
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitAnnotatedType(JCTree.JCAnnotatedType tree) {
        try {
            if (tree.underlyingType.hasTag(Tag.SELECT)) {
                JCTree.JCFieldAccess access = (JCTree.JCFieldAccess)tree.underlyingType;
                this.printExpr(access.selected, 15);
                this.print('.');
                this.printTypeAnnotations(tree.annotations);
                this.print(access.name);
            } else if (tree.underlyingType.hasTag(Tag.TYPEARRAY)) {
                this.printBaseElementType(tree);
                this.printBrackets(tree);
            } else {
                this.printTypeAnnotations(tree.annotations);
                this.printExpr(tree.underlyingType);
            }

        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }

    public void visitTree(JCTree tree) {
        try {
            this.print("(UNKNOWN: ");
            this.print(tree.getTag());
            this.print(')');
            this.println();
        } catch (IOException var3) {
            throw new UncheckedIOException(var3);
        }
    }
}
