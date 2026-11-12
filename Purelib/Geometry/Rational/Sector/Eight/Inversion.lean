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
  {value : Canonical}
    (safe : Safe sector value) (residualNonzero : value - sector.rep ≠ 0) :
    1 < Norm.Basic.normSq ((Canonical.gamma * (value - sector.rep))⁻¹) := by
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have productNonzero : Canonical.gamma * (value - sector.rep) ≠ 0 :=
    Field.mul_ne_zero_direct gammaNonzero residualNonzero
  have productNormPositive := Norm.Basic.normSq_pos productNonzero
  have productNormLtOne : Norm.Basic.normSq (Canonical.gamma * (value -
    sector.rep)) < 1 := by
    rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
    calc
      2 * Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) safe
      _ = 1 := by decide
  rw [Field.inv_eq, Field.normSq_inv _ productNonzero]
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Norm.Basic.normSq (Canonical.gamma * (value - sector.rep))) _
      productNormPositive
  calc
    1 * Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) =
        Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) :=
      Fraction.Field.one_mul _
    _ < 1 := productNormLtOne
    _ = (Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)))⁻¹ *
          Norm.Basic.normSq (Canonical.gamma * (value - sector.rep)) :=
      (Fraction.Field.inv_mul_cancel _
        productNormPositive.ne').symm

/-- Squared norm of the numerator created by the safe inverse chart. -/
theorem transformed_difference_normSq
    {sector : Sector} (left right : Canonical) :
    Norm.Basic.normSq
        ((Canonical.gamma * (right - sector.rep)) -
          (Canonical.gamma * (left - sector.rep))) =
      2 * Norm.Basic.normSq (left - right) := by
  have numeratorIdentity :
      (Canonical.gamma * (right - sector.rep)) -
          (Canonical.gamma * (left - sector.rep)) =
        -(Canonical.gamma * (left - right)) := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im,
        Canonical.gamma] <;>
      ring1
  rw [numeratorIdentity, Norm.Basic.normSq_neg, Norm.Basic.normSq_mul,
    Constants.normSq_gamma]

end Purelib.Geometry.Rational.Sector.Eight.Inversion

section

namespace Purelib.Geometry.Rational.Sector.Eight.Inversion

/-- Explicit-inverse form of the affine error calculation. -/
private theorem
  inversion_difference_normSq_explicit
    {sector : Sector} {left right : Canonical}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    Norm.Basic.normSq
        (Canonical.inv (Canonical.gamma * (left - sector.rep)) -
          Canonical.inv (Canonical.gamma * (right - sector.rep))) =
      Norm.Basic.normSq (left - right) /
        (2 * Norm.Basic.normSq (left - sector.rep) * Norm.Basic.normSq
          (right - sector.rep)) := by
  have leftInverse :
      Canonical.inv (Canonical.gamma * (left - sector.rep)) =
        Field.inv (Canonical.gamma * (left - sector.rep)) :=
    Field.inv_eq (Canonical.gamma * (left - sector.rep))
  have rightInverse :
      Canonical.inv (Canonical.gamma * (right - sector.rep)) =
        Field.inv (Canonical.gamma * (right - sector.rep)) :=
    Field.inv_eq (Canonical.gamma * (right - sector.rep))
  rw [leftInverse, rightInverse]
  have gammaNonzero : Canonical.gamma ≠ 0 := by decide
  have leftProductNonzero : Canonical.gamma * (left - sector.rep) ≠ 0 :=
    Field.mul_ne_zero_direct gammaNonzero leftNonzero
  have rightProductNonzero : Canonical.gamma * (right - sector.rep) ≠ 0 :=
    Field.mul_ne_zero_direct gammaNonzero rightNonzero
  let leftProduct := Canonical.gamma * (left - sector.rep)
  let rightProduct := Canonical.gamma * (right - sector.rep)
  have inverseDifference :
      Field.inv leftProduct - Field.inv rightProduct =
        Field.inv leftProduct * (rightProduct - leftProduct) * Field.inv
          rightProduct :=
    Field.inverse_sub_inverse_direct leftProductNonzero rightProductNonzero
  rw [inverseDifference,
    Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Field.normSq_inv _
      leftProductNonzero,
    Field.normSq_inv _ rightProductNonzero]
  have numeratorNorm :
      Norm.Basic.normSq (rightProduct - leftProduct) =
        2 * Norm.Basic.normSq (left - right) := by
    exact transformed_difference_normSq left right
  have leftProductNorm : Norm.Basic.normSq leftProduct =
      2 * Norm.Basic.normSq (left - sector.rep) := by
    dsimp only [leftProduct]
    rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
  have rightProductNorm : Norm.Basic.normSq rightProduct =
      2 * Norm.Basic.normSq (right - sector.rep) := by
    dsimp only [rightProduct]
    rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
  rw [leftProductNorm, rightProductNorm]
  rw [numeratorNorm]
  exact Fraction.ScaledProduct.inverse_error_fraction_direct
    (Norm.Basic.normSq (left - sector.rep))
    (Norm.Basic.normSq (left - right))
    (Norm.Basic.normSq (right - sector.rep))

end Purelib.Geometry.Rational.Sector.Eight.Inversion

end

namespace Purelib.Geometry.Rational.Sector.Eight.Inversion

/-- Exact affine error propagation through the safe inverse chart. This identity explains why a scalar error bound must
be accompanied by residual separation before the projective tail is converted back to an affine box. -/
theorem inversion_difference_normSq
    {sector : Sector} {left right : Canonical}
    (leftNonzero : left - sector.rep ≠ 0)
    (rightNonzero : right - sector.rep ≠ 0) :
    Norm.Basic.normSq
        ((Canonical.gamma * (left - sector.rep))⁻¹ -
          (Canonical.gamma * (right - sector.rep))⁻¹) =
      Norm.Basic.normSq (left - right) /
        (2 * Norm.Basic.normSq (left - sector.rep) * Norm.Basic.normSq
          (right - sector.rep)) := by
  exact inversion_difference_normSq_explicit
    leftNonzero rightNonzero

end Purelib.Geometry.Rational.Sector.Eight.Inversion

end

end
