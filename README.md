# Property Checker

The Property Checker is a checker developed using the Checker Framework for Java. The Checker Framework allows programmers to leverage Java annotations to create pluggable Java type systems. Unlike other checkers in the CF, the Property Checker allows users to specify their own type qualifiers and qualifier hierarchies using a simple definition language.

For example, a non-null qualifier can be defined by the following line:
`annotation NonNull() java.lang.Object :<==> "§subject§ != null" for "true";`

An object `o` has the type `@NonNull Object` if the specified property, `o != null` always evaluates to `true`.

If the Property Checker is not able to completely prove a program's correctness, it outputs a JML translation, in which all property qualifiers have been translated into specification clauses in the Java Modeling Language (JML). This translation can be given to a deductive verification tool like KeY or OpenJML to prove the parts of the program which the checker was not able to prove. This approach combines the scalability and easy-of-use of pluggable type system with the power of deductive verification.

See the folder `tests` for examples.

To build the Property Checker, run `./gradlew assemble`. The file `property-checker.jar` will be generated in the main directory. To be able to run the Property Checker, the files `property-checker.jar`, `checker-qual.jar`, and `javac` (not the regular Java compiler, but the one included here!) must be kept in the same directory.

To run the checker, use the following command:

```
./javac \
-cp property-checker.jar:\
<qualifier_files> \
-processor edu.kit.iti.checker.property.checker.PropertyChecker \
<files_to_check> \
-APropertyChecker_inDir=<your_project_root> \
-APropertyChecker_outDir=<out_dir> \
-APropertyChecker_lattices=<lattice_file> \
-APropertyChecker_qualPkg=<qual_pkg> \
-APropertyChecker_jmlDialect=<jml_dialect> \
-APropertyChecker_translationOnly=<translation_only>
```

where

* `./java` is not the regular Java compiler, but the one included with the Property Checker.
* `<lattice_file>` is the file containing the definition of your qualifier hierarchy. You can specify multiple files by separating them with a comma `,`.
* `<qualifier_files>` are the class files (or a JAR file containing the class files) for all annotations used in your qualifier hierarchy.
* `<files_to_check>` is the name of the file(s) which should be type-checked.
* `<your_project_root>` is the root directory for the source code of the project which should be checked. This is indeed redundant with the previous option. It is there because it is necessary for the Property Checker to know not just the files it should check, but also the file/package structure of the project.
* `<out_dir>` is the directory to which the JML translation should be written.
* `<qual_pkg>` is the fully qualified name of the package containing all annotations.
* `<jml_dialect>` is either `key` or `openjml` depending on the JML dialect that should be used for the translation. The default is `key`.
* `<translation_only>` is `true` if you want to only run the JML translator without running the Property Checker beforehand. The default is `false`.

