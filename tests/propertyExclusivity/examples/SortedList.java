import edu.kit.kastel.property.subchecker.lattice.case_study_qual.*;
import edu.kit.kastel.property.subchecker.exclusivity.qual.*;

import com.sun.tools.javac.util.List;

import CircularList.Node;
import edu.kit.kastel.property.checker.qual.*;

// Used annotations:
//   @NodeProp: subject.size == subject._computeSize();
//   @Sorted: subject.isSorted()
//   @DatumProp: any independent property on the data in the list
//   @Length(a,b): a <= subject.size <= b
//   @IdenticalTo(obj): subject == obj
public class SortedList {
    
    public static class Node {
        
        @Pure
        public static boolean isSorted(Node n) {
            return n == null || n.next == null || n.datum <= n.next.datum && isSorted(n.next);
        }

        private @RecvDep @DatumProp int datum;

        private
        @RecvDep
        @Nullable @Length(min="this.size - 1", max="this.size - 1") @Sorted
        Node next;

        private @RecvDep @Positive int size;

        @Pure
        public
        @Length(min="1", max="1") @Sorted
        Node(int datum) {
            this.size = 1;
            this.datum = datum;
            this.next = null;
        }

        @Pure
        public @IdenticalTo("datum") @DatumProp int getDatum() {
            return datum;
        }

        @Pure
        public @Positive @IdenticalTo("size") int size(@PropSafe Node this) {
            return size;
        }

        @Pure
        public @ReadOnly Node getNextRO() {
            return next;
        }

        @Pure
        public @ShrMut Node getNext(@ShrMut Node this) {
            return next;
        }

        @Pure
        public
        @Immutable
        @Nullable @Sorted @Length(min="this.size - 1", max="this.size - 1")
        @IdenticalTo("next") Node getNextImmut(@Immutable Node this) {
            return next;
        }

        @Pure
        public @ExclMut @NodeProp Node takeOverNext(@ExclMut @NodeProp -> @ReadOnly Node this) {
            return next;
        }

        @Pure
        @Ghost("@Positive int n")
        @Ghost("@Positive int m")
        public @DatumProp int get(
                @PropSafe @Length(min="n", max="m") Node this,
                @Interval(min="0", max="n") int index) {
            if (index == 0) {
                return datum;
            } else {
                return next.get@(index - 1);
            }
        }

        @Ghost("@NonNegative int n")
        @Ghost("@NonNegative int m")
        public void insert(
                   @ExclMut @Length(min="n", max="m")     @Sorted
                -> @ExclMut @Length(min="n+1", max="m+1") @Sorted Node this,
                @Immutable int datum) {            
            if (next == null) {
                if (this.datum >= datum) {
                    this.next = new Node(this.datum); // next: Length(1), this: @Unobservable
                    this.datum = datum;
                } else {
                    this.next = new Node(datum); // next: Length(1), this: @Unobservable
                }
            } else {
                if (this.datum >= datum) {
                    this.next.insert(this.datum); // next: Length(n), this: @Unobservable
                    this.datum = datum;
                } else {
                    this.next.insert(datum); // next: Length(n), this: @Unobservable
                }
            }

            ++this.size;
            // Here at the method return, we test if this: @Observable,
            // i.e., if all field properties hold again
        }
    }
    

    @ExclMut
    private int[] cacheIndices = new int[3] {-1, -1, -1};
    
    @ExclMut
    @Refinement("∀ int i. 0 ≤ i < 3 ∧ cacheIndices[i] ≥ 0 → getWithoutCache(cacheIndices[i]) == cacheValues[i]")
    private int[] cacheValues = new int[3] {-1, -1, -1};
    
    private
    @RecvDep
    @Nullable @Sorted
    Node head;

    @ListLength(min="0", max="0") @ListSorted
    public SortedList() { }

    @Ghost("@NonNegative int n")
    @Ghost("@NonNegative int m")
    public void insert(
               @ExclMut @ListLength(min="n", max="m")     @ListSorted
            -> @ExclMut @ListLength(min="n+1", max="m+1") @ListSorted SortedList this,
            int datum) {
        invalidateCache();
        if (head == null) {
            head = new Node(datum);
        } else {
            head.insert(datum);
        }
    }

    @Ghost("@NonNegative int n")
    @Ghost("@NonNegative int m")
    public int removeFirst(
            @ExclMut @ListLength(min="n+1", max="m+1") @ListSorted
         -> @ExclMut @ListLength(min="n", max="m")     @ListSorted SortedList this) {
        invalidateCache();
        int datum = head.getDatum();
        head = head.takeOverNext();
        return datum;
    }

    @Pure
    public @DatumProp int getFirst(
            @PropSafe @Length(min="1", max="Integer.MAX_VALUE") SortedList this) {
        return head.getDatum();
    }

    @Ghost("@Positive int n")
    @Ghost("@Positive int m")
    public @DatumProp int get(
            @PropSafe @Length(min="n", max="m") SortedList this,
            @Interval(min="0", max="n") int index) {
        if (inCache(index)) return getFromCache(index)
        
        @DatumProp int result = getWithoutCache(index);
        putInCache(index, result);
        return cache;
    }

    @Ghost("@Positive int n")
    @Ghost("@Positive int m")
    public @DatumProp int getWithoutCache(
            @PropSafe @Length(min="n", max="m") SortedList this,
            @Interval(min="0", max="n") int index) {
        return head.get(index);
    }

    @JMLClause("ensures head != null ==> \result == head.size")
    @JMLClause("ensures head == null ==> \result == 0")
    @Pure
    public @NonNegative int size() {
        if (head == null) {
            return 0;
        } else {
            return head.size();
        }
    }
}
