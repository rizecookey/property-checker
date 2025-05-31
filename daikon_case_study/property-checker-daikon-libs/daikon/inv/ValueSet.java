package daikon.inv;

import java.io.*;
import java.util.*;
import daikon.*;

public abstract class ValueSet {

  static final long serialVersionUID = 20020122L;

  protected ValueSet(int max_values) {}

  static final int DEFAULT_MAX_VALUES = 44;

  public static ValueSet factory(VarInfo var_info) {}

  public abstract void add(Object v1);

  protected abstract void add_stats(ValueSet other);

  public abstract String repr_short();

  public void add(ValueSet other) {}

  public static class ValueSetScalar extends ValueSet {

    static final long serialVersionUID = 20031017L;
    long min_val = Long.MAX_VALUE;
    long max_val = Long.MIN_VALUE;

    public ValueSetScalar(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public long min() {}

    public long max() {}

    public String repr_short() {}
  }

  public static class ValueSetFloat extends ValueSet {

    static final long serialVersionUID = 20031017L;
    double min_val;
    double max_val;
    boolean can_be_NaN = false;

    public ValueSetFloat(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public double min() {}

    public double max() {}

    public boolean canBeNaN() {}

    public String repr_short() {}
  }

  public static class ValueSetScalarArray extends ValueSet {

    static final long serialVersionUID = 20031017L;
    long min_val = Long.MAX_VALUE;
    long max_val = Long.MIN_VALUE;
    int max_length = 0;
    int elem_cnt = 0;
    int nonsingleton_arr_cnt = 0;

    public ValueSetScalarArray(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public long min() {}

    public long max() {}

    public int elem_cnt() {}

    public int nonsingleton_arr_cnt() {
    }

    public int max_length() {}

    public String repr_short() {}
  }

  public static class ValueSetFloatArray extends ValueSet {

    static final long serialVersionUID = 20031017L;
    double min_val = Long.MAX_VALUE;
    double max_val = Long.MIN_VALUE;
    boolean can_be_NaN = false;
    int max_length = 0;
    int elem_cnt = 0;
    int nonsingleton_arr_cnt = 0; // number of arrays with 2 or more elements

    public ValueSetFloatArray(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public double min() {}

    public double max() {}

    public boolean canBeNaN() {}

    public int elem_cnt() {}

    public int nonsingleton_arr_cnt() {}

    public int max_length() {}

    public String repr_short() {}
  }

  public static class ValueSetString extends ValueSet {

    static final long serialVersionUID = 20031017L;

    public ValueSetString(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public String repr_short() {}
  }

  public static class ValueSetStringArray extends ValueSet {

    static final long serialVersionUID = 20031017L;
    int elem_cnt = 0;
    int nonsingleton_arr_cnt = 0;

    public ValueSetStringArray(int max_values) {}

    public void add(Object v1) {}

    protected void add_stats(ValueSet other) {}

    public int elem_cnt() {}

    public int nonsingleton_arr_cnt() {}

    public String repr_short() {}
  }
}
