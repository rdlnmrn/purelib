module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Basic
import Purelib.Data.ComplexContinuedFraction.Encoding.Sector.Contraction
import Purelib.Data.Gaussian.Basic
public import Purelib.Data.Gaussian.Constants
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

/-!
# Choice-free completed CCL blocks

Raw words, decoder matrices, determinants, and the strict post-inversion norm
estimate are all finite computations over constructive Gaussian fractions.
-/

@[expose] public section

namespace Purelib.Data.CCL.Encoding.Block.Descent

open Purelib.Data.ComplexContinuedFraction.Encoding
open Purelib.Data.Gaussian
open Purelib.Data.Rat
/-- Sector contraction strictly decreases the gamma-scaled residual numerator norm relative to a nonzero denominator.

The supplied value lies in the closed norm band, the retained sector contains it, and the original numerator equals
value times denominator. The conclusion concerns that same displayed numerator and denominator. -/
theorem inversion_stage_descent {value numerator denominator :
  Basic.Canonical}
    (denominatorNonzero : denominator ≠ 0)
    (band : Data.ComplexContinuedFraction.Encoding.Sector.Band value) (sector :
      Data.ComplexContinuedFraction.Encoding.Sector)
    (holds : sector.Holds value)
    (numeratorIdentity : numerator = value * denominator) :
    Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (numerator - sector.rep * denominator)) <
      Data.Gaussian.Norm.Basic.normSq denominator := by
  have differenceIdentity :
      numerator - sector.rep * denominator =
        (value - sector.rep) * denominator := by
    rw [numeratorIdentity]
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im] <;> ring1
  have sectorContraction := Data.ComplexContinuedFraction.Encoding.Sector.contraction band sector holds
  have factorContraction :
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < (1 : Fraction.Rational) := by
    calc
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) sectorContraction
      _ = 1 := by decide
  have denominatorPositive := Norm.Basic.normSq_pos denominatorNonzero
  calc
    Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (numerator - sector.rep * denominator)) =
        (2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep)) * Data.Gaussian.Norm.Basic.normSq denominator := by
      rw [differenceIdentity, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, Constants.normSq_gamma]
      ring1
    _ < 1 * Data.Gaussian.Norm.Basic.normSq denominator :=
      Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        factorContraction denominatorPositive
    _ = Data.Gaussian.Norm.Basic.normSq denominator := Fraction.Field.one_mul _

/-- A nonzero sector residual from the closed norm band gives reciprocal gamma-scaled squared norm strictly above one.
-/
theorem postInversion_norm_gt_one {value : Basic.Canonical}
    (band : Data.ComplexContinuedFraction.Encoding.Sector.Band value) (sector :
      Data.ComplexContinuedFraction.Encoding.Sector)
    (holds : sector.Holds value) (residualNonzero : value - sector.rep ≠ 0) :
    1 < Data.Gaussian.Norm.Basic.normSq ((Basic.Canonical.gamma * (value - sector.rep))⁻¹) := by
  have gammaNonzero : Basic.Canonical.gamma ≠ 0 := by decide
  have productNonzero : Basic.Canonical.gamma * (value - sector.rep) ≠ 0 :=
    Field.mul_ne_zero_direct gammaNonzero residualNonzero
  have sectorContraction := Data.ComplexContinuedFraction.Encoding.Sector.contraction band sector holds
  have productNormPositive := Norm.Basic.normSq_pos productNonzero
  have productNormLtOne :
      Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep)) < 1 := by
    rw [Norm.Basic.normSq_mul, Constants.normSq_gamma]
    calc
      2 * Data.Gaussian.Norm.Basic.normSq (value - sector.rep) < 2 * (1 / 2 : Fraction.Rational) :=
        Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          (by decide) sectorContraction
      _ = 1 := by decide
  rw [Field.inv_eq, Field.normSq_inv _ productNonzero]
  apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep))) _ productNormPositive
  calc
    1 * Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep)) =
        Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep)) :=
      Fraction.Field.one_mul _
    _ < 1 := productNormLtOne
    _ = (Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep)))⁻¹ *
          Data.Gaussian.Norm.Basic.normSq (Basic.Canonical.gamma * (value - sector.rep)) :=
      (Fraction.Field.inv_mul_cancel _ productNormPositive.ne').symm
end Purelib.Data.CCL.Encoding.Block.Descent

end
