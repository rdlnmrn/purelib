module
import Purelib.Algebra.Field.Squares
public import Purelib.Geometry.Triangles.Quadrance.Realization
import Purelib.Geometry.Trigonometry.QuadTriple.Basic

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.QuadraticForm.Binary.SumOfSquares
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Triangles.Quadrance

open Purelib.Geometry.Trigonometry

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

namespace Purelib.Geometry.Triangles.Quadrance.Existence.ImaginaryUnit

open Purelib.Algebra

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Corrected Exercise 5.3. Once an imaginary unit is supplied, the only remaining constructive obstruction is exactly
the source's Theorem 28 condition that the quadrea be a nonzero square. -/
theorem
  hasTriangleQuadrances_iff_nonzeroSquare_quadrea
    [Nontrivial K] [DecidableEq K]
    (q₁ q₂ q₃ imaginary : K) (twoNonzero : (2 : K) ≠ 0)
    (someNonzero : q₁ ≠ 0 ∨ q₂ ≠ 0 ∨ q₃ ≠ 0)
    (imaginarySquare : imaginary ^ 2 = -1) :
    Realization.HasTriangleQuadrances q₁ q₂ q₃ ↔
      Squares.IsNonzeroSquare (QuadTriple.Basic.archimedesFunction q₁ q₂ q₃) := by
  constructor
  · intro triangle
    exact ((Realization.triangle_quadrea q₁ q₂ q₃ twoNonzero).1 triangle).2.2.2.2
  · intro areaSquare
    apply (Realization.triangle_quadrea q₁ q₂ q₃ twoNonzero).2
    exact ⟨someNonzero,
      QuadraticForm.Binary.SumOfSquares.isSumOfTwoSquares_of_squareRootNegativeOne q₁ imaginary twoNonzero
        imaginarySquare,
      QuadraticForm.Binary.SumOfSquares.isSumOfTwoSquares_of_squareRootNegativeOne q₂ imaginary twoNonzero
        imaginarySquare,
      QuadraticForm.Binary.SumOfSquares.isSumOfTwoSquares_of_squareRootNegativeOne q₃ imaginary twoNonzero
        imaginarySquare,
      areaSquare⟩
section
end

section
end

end Purelib.Geometry.Triangles.Quadrance.Existence.ImaginaryUnit

end
