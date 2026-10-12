module
import Purelib.Geometry.Projective.Line.Basic
import Purelib.LinearAlgebra.Coordinates2.Matrix

public import Purelib.Geometry.Projective.Line.Matrix
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Basic

@[expose] public section
namespace Purelib.Data.ContinuedFraction.Matrix
open Purelib.Geometry.Projective.Line
open Purelib.Geometry.Projective.Line.Matrix

open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Construct the continued-fraction substitution matrix with first row t and mu and second row one and zero. -/
def cf [Zero K] [One K] (t μ : K) : Matrix2 K := ⟨t, μ, 1, 0⟩

section CommRing
variable {K : Type*} [CommRing K]

/-- The substitution matrix sends the affine point y to the homogeneous pair t times y plus mu over y.

The two original coefficients determine the new numerator, and the denominator retains the supplied affine coordinate.
-/
theorem cf_substitution (t μ y : K) :
    act (cf t μ) (Proj.affine y) = ⟨t * y + μ, y⟩ := by
  ext <;>
    (simp only [act, cf, Proj.affine, mul_one, one_mul, add_zero, -eq_self, -iff_self]
     rfl)

open Purelib.LinearAlgebra.Coordinates2 renaming Matrix -> Matrix2 in
/-- Right multiplication by the substitution matrix updates the retained matrix columns by the displayed recurrence.

The first column combines both original columns using the retained coefficient t; the second is the original first
column scaled by mu. -/
theorem mul_cf (M : Matrix2 K) (t μ : K) :
    Matrix2.mul M (cf t μ) =
      ⟨M.a * t + M.b, M.a * μ, M.c * t + M.d, M.c * μ⟩ := by
  ext <;>
    (simp only [Matrix2.mul, cf, mul_zero, mul_one, add_zero, -eq_self, -iff_self]
     rfl)

end CommRing

end Purelib.Data.ContinuedFraction.Matrix
end
