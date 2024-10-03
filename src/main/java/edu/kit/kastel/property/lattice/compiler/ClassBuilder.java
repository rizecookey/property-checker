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
package edu.kit.kastel.property.lattice.compiler;

import com.google.common.collect.Streams;
import edu.kit.kastel.property.config.Config;
import edu.kit.kastel.property.util.FileUtils;

import javax.tools.JavaCompiler;
import javax.tools.JavaFileObject;
import javax.tools.StandardJavaFileManager;
import javax.tools.ToolProvider;
import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.net.URLClassLoader;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.StringJoiner;
import java.util.stream.Collectors;

@SuppressWarnings("nls")
public class ClassBuilder {

    protected JavaCompiler compiler = ToolProvider.getSystemJavaCompiler();
    protected StandardJavaFileManager fileManager = compiler.getStandardFileManager(null, null, null);
    protected String className;
    protected StringJoiner sj;
    protected Path dir;
    
    public ClassBuilder(String className) {
    	this(className, Config.TEMP_DIR_DELETE_ON_EXIT_DEFAULT);
    }

    public ClassBuilder(String className, boolean deleteOnExit) {
        this.className = className;

        sj = new StringJoiner(
                "\n\n",
                String.format("package %s;\n\npublic final class %s {\n\n\tprivate %s() { }\n\n", Config.CHECKERS_PACKAGE, className, className),
                "\n}");

        try {
        	dir = Files.createTempDirectory("property-checker");
        	if (deleteOnExit) {
        		Runtime.getRuntime().addShutdownHook(new Thread() {
        		    @Override
        		    public void run() {
        		        try {
        		            org.apache.commons.io.FileUtils.deleteDirectory(dir.toFile());
        		        } catch (IOException e) {
        		            e.printStackTrace();
        		        }
        		    }
        		});
        	}
        } catch (IOException e1) {
        	e1.printStackTrace();
        	System.exit(1);
        }
    }
    
    public Class<?> compile(URLClassLoader parentLoader) {
    	try(URLClassLoader classLoader = new URLClassLoader(new URL[] {dir.toUri().toURL()}, parentLoader)) {
    		File file = Paths.get(dir.toString(), Config.CHECKERS_PACKAGE, className + ".java").toFile();    		
    		FileUtils.writeToFile(file, sj.toString());

    		@SuppressWarnings("unchecked")
    		Iterable<? extends JavaFileObject> src = fileManager.getJavaFileObjectsFromFiles(
    				org.apache.commons.io.FileUtils.listFiles(dir.toFile(), new String[] {"java"}, true));
    		
    		ClassLoader grandparentLoader = parentLoader.getParent();
    		String sep = System.getProperty("path.separator");
    		String classPathStr = System.getProperty("java.class.path")
                    + sep
                    + Arrays.stream(parentLoader.getURLs()).map(URL::toString).collect(Collectors.joining(sep));
    		
    		if (grandparentLoader instanceof URLClassLoader) {
    		    classPathStr +=
    		            sep +
    		            Arrays.stream(((URLClassLoader) grandparentLoader).getURLs()).map(URL::toString).collect(Collectors.joining(sep));
    		}
    		
    		JavaCompiler.CompilationTask task = compiler.getTask(
    				null,
    				fileManager,
    				null,
    				Arrays.asList("-classpath", classPathStr),
    				null,
    				src);
    		task.call();

    		return classLoader.loadClass(Config.CHECKERS_PACKAGE + "." + className);
    	} catch (RuntimeException | IOException | ClassNotFoundException e) {
			return null;
    	}
    }

    public void addMethod(String returnType, String methodName, String expression, String[] paramTypes, String[] paramNames, String comment) {
        StringBuilder sb = new StringBuilder();

        sb.append(String.format("\t// %s\n", comment));
        sb.append(String.format("\tpublic static %s %s(", returnType, methodName));
        sb.append(
                Streams
                .zip(Arrays.stream(paramTypes), Arrays.stream(paramNames), (t,n) -> t + " " + n)
                .collect(Collectors.joining(", ")));

        String javaExpression = expression;

        for (String paramName : paramNames) {
            javaExpression = javaExpression.replace('§' + paramName + '§', paramName);
        }

        sb.append(String.format(") {\n\t\treturn %s;\n\t}", javaExpression));

        sj.add(sb.toString());
    }

    public void addMethod(String methodName, String expression, String[] paramTypes, String[] paramNames, String comment) {
        addMethod("boolean", methodName, expression, paramTypes, paramNames, comment);
    }

}
