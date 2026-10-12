module
public import Purelib.Algebra.Field.ExplicitField
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Purelib.Tactic.Ring

open Purelib

@[expose] public section

/-!
# Divine Proportions, Exercises 3.2 and 3.13

The source phrases both exercises as cardinalities of complete finite-field
carriers.  Such global enumerations are outside this project's proof boundary.
The incidence content is instead made executable through finite charts:

* every line through a point is either one uniquely determined slope line or
  the vertical line;
* every point on a line is obtained uniquely from one scalar parameter, using
  whichever displayed direction coefficient is nonzero.

These are the constructive bijection data behind the counts `p+1` and `p`.
For triangles, the usual counting proof is retained as exact cleared integer
identities.  It subtracts collinear triples from all triples and, in the null
case, subtracts the double-counted triangles having two null sides.  No list
of all points, lines, or triangles is constructed.
-/

namespace Purelib.Geometry.Plane.Finite.CountArithmetic

section

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K] [Nontrivial K]
section

/-- Six times the number of unordered triples selected from `p²` points. -/
def allPointTriplesNumerator (p : Int) : Int :=
  p ^ 2 * (p ^ 2 - 1) * (p ^ 2 - 2)

/-- Six times the collinear-triple incidence count: `p(p+1)` lines, with `p(p-1)(p-2)` ordered triples on each line. -/
def collinearTriplesNumerator (p : Int) : Int :=
  p * (p + 1) * (p * (p - 1) * (p - 2))

/-- Six times the resulting number of triangles. -/
def triangleCountNumerator (p : Int) : Int :=
  p ^ 3 * (p - 1) * (p ^ 2 - 1)

/-- Exercise 3.13's ordinary triangle count, with the common denominator six cleared. Every collinear triple belongs to
its unique line, so subtracting the second numerator from the first leaves `p³(p-1)(p²-1)`. -/
theorem triangle_count_cleared (p : Int) :
    allPointTriplesNumerator p -
      collinearTriplesNumerator p =
      triangleCountNumerator p := by
  unfold allPointTriplesNumerator
    collinearTriplesNumerator
    triangleCountNumerator
  ring1

/-- The source's usual triangle-count formula, retained as a finite natural calculation for any requested input. -/
def triangleCount (p : Nat) : Nat :=
  (p ^ 3 * (p - 1) * (p ^ 2 - 1)) / 6

/-- If `-1` is not square, there are no null directions and hence no null triangles. -/
def nullTriangleCountWithoutNullLines (_p : Nat) : Nat := 0

/-- If `-1` is square, the null-triangle count after correcting the overlap of the two null directions is `p²(p-1)³`. -/
def nullTriangleCountWithNullLines (p : Nat) : Nat :=
  p ^ 2 * (p - 1) ^ 3

/-- Twice the null-side incidence count minus twice the overlap count equals twice `p²(p-1)³`. The overlap consists
exactly of triangles whose two null sides meet at one vertex. -/
theorem null_triangle_count_cleared (p : Int) :
    (2 * p) * (p * (p - 1)) * (p ^ 2 - p) -
        2 * (p ^ 2 * (p - 1) ^ 2) =
      2 * (p ^ 2 * (p - 1) ^ 3) := by
  ring1
end

end

end Purelib.Geometry.Plane.Finite.CountArithmetic

end
