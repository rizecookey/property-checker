package daikon;

import java.io.*;
import java.util.*;
import daikon.inv.*;

public class PptName {

  static final long serialVersionUID = 20020122L;

  public PptName(String name) {}

  public PptName(/*@nullable@*/ String className, /*@nullable@*/ String methodName, String pointName) {}

  /*@pure@*/ public String name() {}

  /*@pure@*/ public String getName() {}

  public /*@nullable@*/ String getFullClassName() {}

  public /*@nullable@*/ String getShortClassName() {}

  public /*@nullable@*/ String getPackageName() {}

  public /*@nullable@*/ String getSignature() {}

  public /*@nullable@*/ String getMethodName() {}

  public /*@nullable@*/ String getNameWithoutPoint() {}

  public /*@nullable@*/ String getPoint() {}

  public int getPointSubscript() {}

  /*@pure@*/ public boolean isObjectInstanceSynthetic() {}

  /*@pure@*/ public boolean isClassStaticSynthetic() {}

  /*@pure@*/ public boolean isGlobalPoint() {}

  /* @ public normal_behavior
    @ ensures \result ==> point != null;
    @ assignable \nothing;
    @*/
  public boolean isExitPoint() {}

  /* @ public normal_behavior
    @ ensures \result ==> point != null;
    @ assignable \nothing;
    @*/
  public boolean isThrowsPoint() {}

  /* @ public normal_behavior
    @ ensures \result ==> point != null;
    @ assignable \nothing;
    @*/
  public boolean isCombinedExitPoint() {}

  /* @ public normal_behavior
    @ ensures \result ==> point != null;
    @ assignable \nothing;
    @*/
  public boolean isNumberedExitPoint() {}

  /* @ public normal_behavior
    @ ensures \result ==> point != null;
    @ assignable \nothing;
    @*/
  public boolean isEnterPoint() {}

  public String exitLine() {}

  /*@pure@*/ public boolean isConstructor() {}

  public String repr() {}

  public PptName makeEnter() {}

  public PptName makeExit() {}

  public PptName makeObject() {}

  public PptName makeClassStatic() {}
}
