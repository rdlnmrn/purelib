module
import Purelib.Data.Rat.Fraction
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.ScaledProduct
public import Purelib.Geometry.Rational.Sector.Eight.Safe
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Data.ComplexContinuedFraction.Encoding

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib.Geometry.Rational.Sector.Eight

section
@[expose] public section

/-!
# Redundant safe regions for constructive CCL output

The canonical CCL encoder uses a disjoint eight-sector table on a normalized
annulus.  Arithmetic needs a redundant output test: an enclosure which
straddles a canonical boundary must still be allowed to choose a sound digit.

This module does not alter the canonical bitstream language.  It records the
weaker local condition actually used by subtraction and inversion.  The open
unit cell centred at a sector representative is one finite, rational way to
certify that condition.
-/

section

namespace Purelib.Geometry.Rational.Sector.Eight.Inversion

/-- Local safety alone gives the strict post-inversion lower norm. The old annulus upper bound was used only to derive
this local inequality. -/
theorem postInversion_norm_gt_one {sector :
  Sector}
  {value : Data.Gaussian.Basic.Canonical}
    (safe : Geometry.Rational.Sector.Eight.Safe sector value) (residualNonzero : value - sector.rep ≠ 0) :
    1 < Data.Gaussian.Norm.Basic.normSq ((Canonical.gamma * (value - sector.rep))⁻¹) := by
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have productNonzero : Canonical.gamma * (value - sector.rep) ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct gammaNonzero residualNonzero
  have productNormPositive := Data.Gaussian.Norm.Basic.normSq_pos productNonzero
  have productNormLtOne : Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value -
    sector.rep)) < 1 := by
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma]
    calc
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) safe
      _ = 1 := by decide
  rw [Data.Gaussian.Field.inv_eq, Data.Gaussian.Field.normSq_inv _ productNonzero]
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value - sector.rep))) _
      productNormPositive
  calc
    1 * Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) =
        Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) :=
      Fraction.Field.one_mul _
    _ < 1 := productNormLtOne
    _ = (Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)))⁻¹ *
          Data.Gaussian.Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) :=
      (Fraction.Field.inv_mul_cancel _
        productNormPositive.ne').symm

/-- Squared norm of the numerator created by the safe inverse chart. -/
theorem transformed_difference_normSq
    {sector : Sector} (left right : Data.Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq
        ((Canonical.gamma * (right - sector.rep)) -
          (Canonical.gamma * (left - sector.rep))) =
      2 * Data.Gaussian.Norm.Basic.normSq (left - right) := by
  have numeratorIdentity :
      (Canonical.gamma * (right - sector.rep)) -
          (Canonical.gamma * (left - sector.rep)) =
        -(Canonical.gamma * (left - right)) := by
    apply Data.Gaussian.Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im,
        Canonical.gamma] <;>
      ring1
  rw [numeratorIdentity, Data.Gaussian.Norm.Basic.normSq_neg, Data.Gaussian.Norm.Basic.normSq_mul,
    Constants.normSq_gamma]

end Purelib.Geometry.Rational.Sector.Eight.Inversion

section

namespace Purelib.Geometry.Rational.Sector.Eight.Inversion

/-- Explicit-inverse form of the affine error calculation. -/
private theorem
  inversion_difference_normSq_explicit
    {sector : Sector} {left right : Data.Gaussian.Basic.Canonical}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq
        (Canonical.inv (Canonical.gamma * (left - sector.rep)) -
          Canonical.inv (Canonical.gamma * (right - sector.rep))) =
      Data.Gaussian.Norm.Basic.normSq (left - right) /
        (2 * Data.Gaussian.Norm.Basic.normSq (left - sector.rep) * Data.Gaussian.Norm.Basic.normSq
          (right - sector.rep)) := by
  have leftInverse :
      Canonical.inv (Canonical.gamma * (left - sector.rep)) =
        Data.Gaussian.Field.inv (Canonical.gamma * (left - sector.rep)) :=
    Data.Gaussian.Field.inv_eq (Canonical.gamma * (left - sector.rep))
  have rightInverse :
      Canonical.inv (Canonical.gamma * (right - sector.rep)) =
        Data.Gaussian.Field.inv (Canonical.gamma * (right - sector.rep)) :=
    Data.Gaussian.Field.inv_eq (Canonical.gamma * (right - sector.rep))
  rw [leftInverse, rightInverse]
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have leftProductNonzero : Canonical.gamma * (left - sector.rep) ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct gammaNonzero leftNonzero
  have rightProductNonzero : Canonical.gamma * (right - sector.rep) ≠ 0 :=
    Data.Gaussian.Field.mul_ne_zero_direct gammaNonzero rightNonzero
  let leftProduct := Canonical.gamma * (left - sector.rep)
  let rightProduct := Canonical.gamma * (right - sector.rep)
  have inverseDifference :
      Data.Gaussian.Field.inv leftProduct - Data.Gaussian.Field.inv rightProduct =
        Data.Gaussian.Field.inv leftProduct * (rightProduct - leftProduct) * Data.Gaussian.Field.inv
          rightProduct :=
    Data.Gaussian.Field.inverse_sub_inverse_direct leftProductNonzero rightProductNonzero
  rw [inverseDifference,
    Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Norm.Basic.normSq_mul, Data.Gaussian.Field.normSq_inv _
      leftProductNonzero,
    Data.Gaussian.Field.normSq_inv _ rightProductNonzero]
  have numeratorNorm :
      Data.Gaussian.Norm.Basic.normSq (rightProduct - leftProduct) =
        2 * Data.Gaussian.Norm.Basic.normSq (left - right) := by
    exact transformed_difference_normSq left right
  have leftProductNorm : Data.Gaussian.Norm.Basic.normSq leftProduct =
      2 * Data.Gaussian.Norm.Basic.normSq (left - sector.rep) := by
    dsimp only [leftProduct]
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma]
  have rightProductNorm : Data.Gaussian.Norm.Basic.normSq rightProduct =
      2 * Data.Gaussian.Norm.Basic.normSq (right - sector.rep) := by
    dsimp only [rightProduct]
    rw [Data.Gaussian.Norm.Basic.normSq_mul, Constants.normSq_gamma]
  rw [leftProductNorm, rightProductNorm]
  rw [numeratorNorm]
  exact Fraction.ScaledProduct.inverse_error_fraction_direct
    (Data.Gaussian.Norm.Basic.normSq (left - sector.rep))
    (Data.Gaussian.Norm.Basic.normSq (left - right))
    (Data.Gaussian.Norm.Basic.normSq (right - sector.rep))

end Purelib.Geometry.Rational.Sector.Eight.Inversion

end

namespace Purelib.Geometry.Rational.Sector.Eight.Inversion

/-- Exact affine error propagation through the safe inverse chart. This identity explains why a scalar error bound must
be accompanied by residual separation before the projective tail is converted back to an affine box. -/
theorem inversion_difference_normSq
    {sector : Sector} {left right : Data.Gaussian.Basic.Canonical}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    Data.Gaussian.Norm.Basic.normSq
        ((Canonical.gamma * (left - sector.rep))⁻¹ -
          (Canonical.gamma * (right - sector.rep))⁻¹) =
      Data.Gaussian.Norm.Basic.normSq (left - right) /
        (2 * Data.Gaussian.Norm.Basic.normSq (left - sector.rep) * Data.Gaussian.Norm.Basic.normSq
          (right - sector.rep)) := by
  exact inversion_difference_normSq_explicit
    leftNonzero rightNonzero

end Purelib.Geometry.Rational.Sector.Eight.Inversion

end

end
