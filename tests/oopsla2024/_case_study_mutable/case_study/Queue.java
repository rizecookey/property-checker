package case_study;

import edu.kit.kastel.property.util.Packing;
import edu.kit.kastel.property.checker.qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;
import edu.kit.kastel.property.subchecker.lattice.qual.*;
import edu.kit.kastel.property.packing.qual.*;
import org.checkerframework.checker.initialization.qual.*;

public class Queue {
    
    public final @Nullable List front;
    public final @Nullable List back;

    @JMLClause("ensures \\result.front == null && \\result.back == null;")
    @JMLClause("assignable \\nothing;")
    public @Okasaki Queue() {
        // :: error: return.type.incompatible
        this(null, null);
    }

    @JMLClause("ensures this.front == front && this.back == back;")
    @JMLClause("assignable \\nothing;")
    // :: error: inconsistent.constructor.type
    public Queue(@Nullable List front, @Nullable List back) {
        this.front = front;
        this.back = back;
    }

    @JMLClause("ensures this.front != null || this.back != null || this.acc != null ==> \\result != null;")
    @JMLClause("assignable this.*;")
    @EnsuresOkasaki("this")
    private void rotate(
            @Unique Queue this) {
        Packing.unpack(this, Queue.class);

        @Unique List acc = null;
        while (this.back != null) {
            if (acc == null) {
                acc.insertFront(this.back.getHead());
                this.back = this.back.stealTail();
            }
        }

        this.front.appendBack(acc);

        Packing.pack(this, Queue.class);
    }


    @JMLClause("ensures this.front != null || this.back != null ==> \result.front != null;")
    @JMLClause("assignable \\nothing;")
    @EnsuresOkasaki("this")
    public void toOkasaki(@Unique Queue this) {
        // :: error: method.invocation.invalid
        if (back == null || (front != null && front.size() >= back.size())) {
            // :: error: return.type.incompatible
            return this;
        } else {
            rotate(null);
        }
    }

    @JMLClause("ensures this.front == null && this.back == null ==> \\result == 0")
    @JMLClause("ensures this.front == null && this.back != null ==> \\result == this.back.size")
    @JMLClause("ensures this.front != null && this.back == null ==> \\result == this.front.size")
    @JMLClause("ensures this.front != null && this.back != null ==> \\result == this.front.size + this.back.size")
    @JMLClause("assignable \\nothing;")
    public int size() {
        return List.size(this.front) + List.size(this.back);
    }

    @JMLClause("assignable \\nothing;")
    public Object peekUnique(@Unique @FrontNonEmpty Queue this) {
        // :: error: method.invocation.invalid
        return front.getHead();
    }

    @JMLClause("assignable \\nothing;")
    public Object peekMaybeAliased(@MaybeAliased @FrontNonEmpty Queue this) {
        // :: error: method.invocation.invalid
        return front.getHead();
    }

    @JMLClause("assignable this.front;")
    public void remove(@Unique @FrontNonEmpty Queue this) {
        Packing.unpack(this, Queue.class);
        front = front.getTail();
        Packing.pack(this, Queue.class);
    }

    @JMLClause("assignable this.front;")
    public void removeIfPresent(@Unique Queue this) {
        if (this.size() > 0) {
            if (this.front != null) {
                // :: error: method.invocation.invalid
                this.remove();
            } else {
                // :: error: method.invocation.invalid
                this.toOkasaki().remove();
            }
        } else {
            return this;
        }
    }

    @JMLClause("assignable this.back;")
    public void insert(
            @Unique Queue this,
            Object o) {
        Packing.unpack(this, Queue.class);
        this.back.insertFront(o);
        Packing.pack(this, Queue.class);
    }
}
