package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Queue {
    
    public @Unique @Nullable List front;
    public @Unique @Nullable List back;

    @JMLClause("ensures this.front == null && this.back == null;")
    @JMLClause("assignable \\nothing;")
    // :: error: okasaki.inconsistent.constructor.type
    public @Okasaki Queue() {
        this(null, null);
    }

    @JMLClause("ensures this.front == front && this.back == back;")
    @JMLClause("assignable \\nothing;")
    @EnsuresReadOnly(value="#1")
    @EnsuresReadOnly(value="#2")
    public Queue(@Unique @Nullable List front, @Unique @Nullable List back) {
        this.front = front;
        this.back = back;
        Packing.pack(this, Queue.class);
    }

    @JMLClause("ensures \\old(this.front) != null || \\old(this.back) != null ==> this.front != null;")
    @EnsuresOkasaki("this")
    // :: error: okasaki.contracts.postcondition.not.satisfied
    private void rotate(
            @Unique Queue this) {
        Packing.unpack(this, Queue.class);

        @Unique List acc = null;
        while (this.back != null) {
            if (acc == null) {
                // :: error: nullness.method.invocation.invalid
                Object backHead = this.back.getHead();
                acc = new List(backHead);
            } else {
                // :: error: nullness.method.invocation.invalid
                int accSize = acc.size();
                // :: error: nullness.method.invocation.invalid
                Object backHead = this.back.getHead();
                // :: error: length.method.invocation.invalid
                acc.insertFront(backHead, accSize, accSize);
            }
            this.back = this.back.stealTail();
        }

        // :: error: nullness.method.invocation.invalid
        int frontSize = this.front.size();
        if (acc != null) {
            // :: error: nullness.method.invocation.invalid
            int accSize = acc.size();
            // :: error: length.method.invocation.invalid :: error: length.argument.type.incompatible
            this.front.appendBack(acc, frontSize, frontSize, accSize, accSize);
        }

        Packing.pack(this, Queue.class);
    }


    @JMLClause("ensures \\old(this.front) != null || \\old(this.back) != null ==> this.front != null;")
    @EnsuresOkasaki("this")
    // :: error: okasaki.contracts.postcondition.not.satisfied
    public void toOkasaki(@Unique Queue this) {
        if (this.back == null) {
            return;
        }

        if (this.front != null) {
            // :: error: nullness.method.invocation.invalid
            int f = this.front.size();
            // :: error: nullness.method.invocation.invalid
            int b = this.back.size();
            if (f >= b) {
                return;
            }
        }

        this.rotate();
    }

    @JMLClause("ensures this.front == null && this.back == null ==> \\result == 0;")
    @JMLClause("ensures this.front == null && this.back != null ==> \\result == this.back.size;")
    @JMLClause("ensures this.front != null && this.back == null ==> \\result == this.front.size;")
    @JMLClause("ensures this.front != null && this.back != null ==> \\result == this.front.size + this.back.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique Queue this) {
        // :: error: sign.return.type.incompatible
        return List.size(this.front) + List.size(this.back);
    }

    @JMLClause("assignable \\strictly_nothing;") @Pure
    public Object peekUnique(@Unique @FrontNonEmpty Queue this) {
        // :: error: nullness.method.invocation.invalid
        return this.front.getHead();
    }

    @JMLClause("assignable \\strictly_nothing;") @Pure
    public Object peekMaybeAliased(@MaybeAliased @FrontNonEmpty Queue this) {
        // :: error: nullness.method.invocation.invalid
        return this.front.getHead();
    }

    @JMLClause("assignable this.front.packed, this.front, this.packed;")
    @EnsuresTopOkasaki("this")
    public void remove(@Unique @FrontNonEmpty Queue this) {
        Packing.unpack(this, Queue.class);
        // :: error: nullness.method.invocation.invalid
        this.front = this.front.stealTail();
        Packing.pack(this, Queue.class);
    }

    @JMLClause("assignable this.front;")
    public void removeIfPresent(@Unique Queue this) {
        if (this.size() > 0) {
            if (this.front == null) {
                this.toOkasaki();
            }
            // :: error: okasaki.method.invocation.invalid
            this.remove();
        }
    }

    @JMLClause("assignable this.back, this.packed;")
    public void insert(
            @Unique Queue this,
            Object o) {
        Packing.unpack(this, Queue.class);
        // :: error: nullness.method.invocation.invalid
        int size = this.back.size();
        // :: error: length.method.invocation.invalid
        this.back.insertFront(o, size, size);
        Packing.pack(this, Queue.class);
    }
}
