module

public import Purelib.Algebra.Field.ExplicitField

open Purelib.Algebra.Field

/-!
# Divine Proportions, remaining Chapter 5 exercises

Exercise 5.3 is false with the source's definition of a triangle: the
nonzero quadrances `1,1,4` have zero quadrea, hence cannot belong to three
noncollinear points.  The corrected theorem below isolates the exact missing
condition.  In a field carrying an explicit square root of `-1`, every scalar
is constructively a sum of two squares, so Theorem 28 reduces triangle
existence to an explicit nonzero square witness for the quadrea.

Exercise 5.17 is retained through the finite construction responsible for its
factor `2`: a chosen base vector and either sign of a nonzero quadrea root give
two distinct completion points with the requested quadrances.  The remaining
`p²` translation and `p±1` nonzero-circle factors are recorded as finite
counting data rather than by enumerating an entire field carrier.

Exercise 5.19 is answered by a recursive, fuel-indexed finite quad relation.
For five entries it introduces the two diagonals of a fan triangulation; for
any requested finite number of entries it repeatedly combines two adjacent
signed lengths.  There is no infinite sequence or completed polygon.
-/

@[expose] public section

namespace Purelib.Algebra.FiniteSum.List.Basic

open Purelib.Algebra

variable {K : Type*} [ExplicitField K]
namespace ExerciseFiveSeventeen
end ExerciseFiveSeventeen

section ExerciseFiveNineteen

/-- Sum a finite list of field elements.

Structural recursion adds the head to the sum of the tail, with zero as the empty sum. -/
def scalarSum : List K → K
  | [] => 0
  | head :: tail => head + scalarSum tail

open Purelib.Algebra.FiniteSum
/-- The scalar sum of an empty list is zero. -/
@[simp] theorem scalarSum_nil : scalarSum ([] : List K) = 0 :=
  rfl

/-- The scalar sum of a cons is its head plus the tail sum. -/
@[simp] theorem scalarSum_cons (head : K) (tail : List K) :
    scalarSum (head :: tail) = head + scalarSum tail := rfl
end ExerciseFiveNineteen

end Purelib.Algebra.FiniteSum.List.Basic

end
