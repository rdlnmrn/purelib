module
import Purelib.Geometry.Projective.Line.Gaussian
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Projective.Line.Basic
public import Purelib.Geometry.Projective.Line.Hermitian

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry.Projective.Line

open Purelib.Geometry.Projective.Line.Basic

open Purelib.Geometry.Projective.Line.Gaussian

open Purelib.Geometry.Projective.Line.Hermitian

section
@[expose] public section

/-!
# Choice-free projective quadrance over constructive Gaussian fractions

This is the finite projective geometry used by the constructive CCL layer.  It
is deliberately separate from `Purelib.CCL.Geometry.Chordal`, whose coordinates are Mathlib's
`Rat`.  Every coordinate here is an explicit quotient of an integer numerator
and a positive integer denominator.
-/

namespace Purelib.Geometry.Projective.Chordal.Basic

/-- The paper's exact squared chordal expression `χ²`. -/
def chordalSq (x y : GaussianLine) :
  Fraction.Rational :=
  Data.Gaussian.Norm.Basic.normSq (x.p * y.q - y.p * x.q) /
    ((Data.Gaussian.Norm.Basic.normSq x.p + Data.Gaussian.Norm.Basic.normSq x.q) *
      (Data.Gaussian.Norm.Basic.normSq y.p + Data.Gaussian.Norm.Basic.normSq y.q))

/-- Express squared chordal quadrance using the alternating product and homogeneous weights. -/
theorem chordalSq_eq_cross (x y : GaussianLine)
  :
    chordalSq x y = Data.Gaussian.Norm.Basic.normSq ((Proj.cross x) y) /
      ((Proj.weight x) * (Proj.weight y)) :=
  rfl

/-- Squared chordal quadrance is nonnegative. -/
theorem chordalSq_nonneg (x y : GaussianLine) :
  0 ≤ chordalSq x y := by
  rw [chordalSq_eq_cross]
  exact Fraction.Order.Field.div_nonneg_direct (Data.Gaussian.Norm.Basic.normSq_nonneg _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Proj.weight_nonneg x)
      (Proj.weight_nonneg y))

/-- Squared chordal error is at most one for valid homogeneous pairs. -/
theorem chordalSq_le_one {x y : GaussianLine}
    (hx : (Proj.HasNonzeroCoordinate x)) (hy : (Proj.HasNonzeroCoordinate y)) :
    chordalSq x y ≤ 1 := by
  rw [chordalSq_eq_cross]
  have denominatorPositive : 0 < (Proj.weight x) * (Proj.weight y) :=
    Fraction.Order.Arithmetic.mul_pos_direct (Proj.weight_pos hx)
      (Proj.weight_pos hy)
  apply (Fraction.Order.Field.div_le_iff_pos denominatorPositive).2
  rw [Fraction.Field.one_mul]
  rw [← Proj.normSq_hermitian_add_normSq_cross x y]
  exact le_add_of_nonneg_left (Data.Gaussian.Norm.Basic.normSq_nonneg (Proj.hermitian x y))

/-- Equivalent homogeneous pairs have zero squared chordal quadrance. -/
theorem chordalSq_eq_zero_of_equivalent {x y :
  GaussianLine}
    (equivalent : x.Equivalent y) : chordalSq x y = 0 := by
  have crossZero : (Proj.cross x) y = 0 := by
    dsimp [Proj.cross, Proj.Equivalent] at equivalent ⊢
    rw [equivalent]
    exact Data.Gaussian.Basic.sub_self _
  rw [chordalSq_eq_cross, crossZero, Data.Gaussian.Norm.Basic.normSq_zero]
  exact Fraction.Field.zero_div_direct _

/-- Squared chordal quadrance is symmetric in the two homogeneous pairs. -/
theorem chordalSq_comm (x y : GaussianLine) :
  chordalSq x y = chordalSq y x := by
  have numerator : y.p * x.q - x.p * y.q =
      -(x.p * y.q - y.p * x.q) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im, Data.Gaussian.Basic.mul_re,
        Data.Gaussian.Basic.mul_im, Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;>
      ring1
  simp only [chordalSq, numerator, Data.Gaussian.Norm.Basic.normSq_neg]
  congr 1
  all_goals ring1
end Purelib.Geometry.Projective.Chordal.Basic

end
