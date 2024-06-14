package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class MinHeapNode {

    public int datum;

    public @Unique @Nullable @HeapProperty MinHeapNode left;
    public @Unique @Nullable @HeapProperty MinHeapNode right;

    boolean leftBalanced;
    boolean rightBalanced;

    public @Positive int size;

    @JMLClause("ensures this.datum == datum && this.left == null && this.right == null && this.size == 1;")
    @JMLClause("assignable \\nothing;") @Pure
    public
    @Unique @HeapProperty
    // :: error: minheap.inconsistent.constructor.type
    MinHeapNode(int datum) {
        this.size = 1;
        this.datum = datum;
        this.left = null;
        this.right = null;
        this.leftBalanced = true;
        this.rightBalanced = true;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);
    }

    @JMLClause("ensures \\result == this.datum;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public int getDatum(@ReadOnly @Nullable MinHeapNode this) {
        return datum;
    }

    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    private void siftDown(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        if (this.left == null || newDatum < this.left.getDatum()) {
            this.siftDownRight(newDatum);
        } else {
            this.siftDownRot(newDatum);
        }
    }

    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    // :: error: minheap.contracts.postcondition.not.satisfied
    private void siftDownRight(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        Packing.unpack(this, MinHeapNode.class);
        if (this.right == null || newDatum < this.right.getDatum()) {
            this.datum = newDatum;
        } else {
            this.datum = this.right.getDatum();
            // :: error: nullness.method.invocation.invalid
            this.right.siftDown(newDatum);
        }
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);
    }

    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    // :: error: minheap.contracts.postcondition.not.satisfied
    private void siftDownRot(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        Packing.unpack(this, MinHeapNode.class);
        if (this.right == null || this.left.getDatum() < this.right.getDatum()) {
            this.datum = this.left.getDatum();
            // :: error: nullness.method.invocation.invalid
            this.left.siftDown(newDatum);
        } else {
            this.datum = this.right.getDatum();
            // :: error: nullness.method.invocation.invalid
            this.right.siftDown(newDatum);
        }
        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);
    }


    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    public int insertThenRemove(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        if (newDatum <= this.datum) {
            return newDatum;
        }
        int result = this.datum;
        this.siftDown(newDatum);
        return result;
    }

    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    public boolean insert(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {

        if (this.left == null || this.right == null) {
            return this.insertDirect(newDatum);
        } else if (leftBalanced && !rightBalanced) {
            return this.insertRight(newDatum);
        } else {
            return this.insertLeft(newDatum);
        }
    }

    @JMLClause("requires this.left != null && this.right != null;")
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    // :: error: minheap.contracts.postcondition.not.satisfied
    private boolean insertLeft(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        Packing.unpack(this, MinHeapNode.class);

        if (newDatum < this.datum) {
            // :: error: nullness.method.invocation.invalid
            this.leftBalanced = this.left.insert(this.datum);
            this.datum = newDatum;
        } else {
            // :: error: nullness.method.invocation.invalid
            this.leftBalanced = this.left.insert(newDatum);
        }
        this.rightBalanced = false;

        this.size = this.size + 1;
        boolean result = leftBalanced && rightBalanced;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);

        return result;
    }

    @JMLClause("requires this.left != null && this.right != null;")
    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    // :: error: minheap.contracts.postcondition.not.satisfied
    private boolean insertRight(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        Packing.unpack(this, MinHeapNode.class);

        if (newDatum < this.datum) {
            // :: error: nullness.method.invocation.invalid
            this.rightBalanced = this.right.insert(this.datum);
            this.datum = newDatum;
        } else {
            // :: error: nullness.method.invocation.invalid
            this.rightBalanced = this.right.insert(newDatum);
        }

        this.size = this.size + 1;
        boolean result = leftBalanced && rightBalanced;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);

        return result;
    }

    @JMLClause("ensures this.size == \\old(this.size) + 1;")
    @JMLClause("assignable \\infinite_union(MinHeapNode n; n.*);")
    // :: error: minheap.contracts.postcondition.not.satisfied
    private boolean insertDirect(
            @Unique @HeapProperty MinHeapNode this,
            int newDatum) {
        Packing.unpack(this, MinHeapNode.class);

        if (this.left == null) {
            if (newDatum < this.datum) {
                this.left = new MinHeapNode(this.datum);
                this.datum = newDatum;
            } else {
                this.left = new MinHeapNode(newDatum);
            }
        } else /*if (this.right == null)*/ {
            if (newDatum < this.datum) {
                this.right = new MinHeapNode(this.datum);
                this.datum = newDatum;
            } else {
                this.right = new MinHeapNode(newDatum);
            }
        }

        this.size = this.size + 1;
        boolean result = leftBalanced && rightBalanced;

        // :: error: initialization.fields.uninitialized
        Packing.pack(this, MinHeapNode.class);

        return result;
    }
}
