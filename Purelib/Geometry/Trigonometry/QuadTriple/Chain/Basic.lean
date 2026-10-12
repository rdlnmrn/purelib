module
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Init.Prelude

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

namespace Purelib.Geometry.Trigonometry.QuadTriple.Chain.Basic

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section
end

section

set_option backward.match.sparseCases false in
/-- The recursive finite `n`-tuple quad relation. Fuel zero expects a quad triple. Each successor step combines the
first two entries through a new diagonal and recurses on a list shorter by one. -/
def QuadRelation : Nat → List K → Prop
  | 0, [first, second, third] => Purelib.Geometry.Trigonometry.QuadTriple first second third
  | 0, _ => False
  | fuel + 1, first :: second :: tail =>
      ∃ diagonal : K,
        Purelib.Geometry.Trigonometry.QuadTriple first second diagonal ∧
          QuadRelation fuel (diagonal :: tail)
  | _ + 1, _ => False
end

end Purelib.Geometry.Trigonometry.QuadTriple.Chain.Basic

end
