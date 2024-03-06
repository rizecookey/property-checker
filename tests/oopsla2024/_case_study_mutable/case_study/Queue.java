package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.case_study_mutable_qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;
import org.checkerframework.dataflow.qual.*;

public final class Queue {
    
    public @Unique List front;
    public @Unique List back;
    public @Unique List acc;

    @JMLClause("ensures \\fresh(this.front) && \\fresh(this.back) && \\fresh(this.acc);")
    @JMLClause("assignable \\nothing;")
    // :: error: okasaki.inconsistent.constructor.type
    public  @Okasaki Queue() {
        this(new List(), new List());
    }

    @JMLClause("ensures this.front == front && this.back == back && \\fresh(this.acc);")
    @JMLClause("assignable \\nothing;")
    @EnsuresReadOnly(value="#1")
    @EnsuresReadOnly(value="#2")
    public Queue(@Unique List front, @Unique List back) {
        this.front = front;
        this.back = back;
        this.acc = new List();
        Packing.pack(this, Queue.class);
    }

    @JMLClause("ensures \\old(this.front).size > 0 || \\old(this.back).size > 0 ==> this.front.size > 0;")
    @JMLClause("ensures \\old(this.front).size + \\old(this.back).size == this.front.size + this.back.size;")
    @EnsuresOkasaki("this")
    // :: error: okasaki.contracts.postcondition.not.satisfied
    private void rotate(
            @Unique Queue this) {
        @NonNegative int frontSize = this.front.size();
        @NonNegative int backSize = this.back.size();
        if (frontSize == 0 && backSize == 0) {
            Packing.unpack(this, Queue.class);
            this.front = this.acc;
            this.back = new List();
            this.acc = new List();
            Packing.pack(this, Queue.class);
        } else if (frontSize == 0) {
            Packing.unpack(this, Queue.class);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            Object backHead = this.back.removeFront(backSize, backSize);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            this.acc.insertFront(backHead, frontSize, frontSize);
            Packing.pack(this, Queue.class);

            this.rotate();
        } else if (backSize == 0) {
            Packing.unpack(this, Queue.class);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            Object h = this.front.removeFront(frontSize, frontSize);
            Packing.pack(this, Queue.class);

            this.rotate();

            Packing.unpack(this, Queue.class);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            this.front.insertFront(h, frontSize - 1, frontSize - 1);
            Packing.pack(this, Queue.class);
        } else {
            Packing.unpack(this, Queue.class);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            Object h = this.front.removeFront(frontSize, frontSize);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            Object backHead = this.back.removeFront(backSize, backSize);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            this.acc.insertFront(backHead, frontSize - 1, frontSize - 1);
            Packing.pack(this, Queue.class);

            this.rotate();

            Packing.unpack(this, Queue.class);
            // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
            this.front.insertFront(h, frontSize, frontSize);
            Packing.pack(this, Queue.class);
        }
    }

    @JMLClause("ensures \\old(this.front).size > 0 || \\old(this.back).size > 0 ==> this.front.size > 0;")
    @JMLClause("ensures \\old(this.front).size + \\old(this.back).size == this.front.size + this.back.size;")
    @EnsuresOkasaki("this")
    // :: error: okasaki.contracts.postcondition.not.satisfied
    public void toOkasaki(@Unique Queue this) {
        if (this.back.size() == 0) {
            return;
        }

        int f = this.front.size();
        int b = this.back.size();
        if (f >= b) {
            return;
        }

        this.rotate();
    }

    @JMLClause("ensures \\result == this.front.size + this.back.size;")
    @JMLClause("assignable \\strictly_nothing;") @Pure
    public @NonNegative int size(@Unique Queue this) {
        // :: error: sign.return.type.incompatible
        return this.front.size() + this.back.size();
    }

    @JMLClause("assignable \\strictly_nothing;") @Pure
    public Object peekUnique(@Unique @FrontNonEmpty Queue this) {
        int frontSize = this.front.size();
        // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
        return this.front.getHead(frontSize, frontSize);
    }

    @JMLClause("assignable \\strictly_nothing;") @Pure
    public Object peekMaybeAliased(@MaybeAliased @FrontNonEmpty Queue this) {
        int frontSize = this.front.size();
        // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
        return this.front.getHead(frontSize, frontSize);
    }

    @EnsuresTopOkasaki("this")
    public void remove(@Unique @FrontNonEmpty Queue this) {
        Packing.unpack(this, Queue.class);
        int frontSize = this.front.size();
        // :: error: length.method.invocation.invalid :: error: sign.argument.type.incompatible
        this.front.removeFront(frontSize, frontSize);
        Packing.pack(this, Queue.class);
    }

    public void removeIfPresent(@Unique Queue this) {
        if (this.size() > 0) {
            if (this.front.size() < this.back.size()) {
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
        int size = this.back.size();
        // :: error: length.method.invocation.invalid
        this.back.insertFront(o, size, size);
        Packing.pack(this, Queue.class);
    }
}
