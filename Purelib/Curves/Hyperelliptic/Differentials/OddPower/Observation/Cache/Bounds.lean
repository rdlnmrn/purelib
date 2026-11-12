module

public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Fixed-box arithmetic observation ceilings

The original polynomial box fold bounds the actual numerator coefficient.
Positive observation-candidate floors bound the unchanged reciprocal and
finite-power processes. The original square-sampling radius denominator is
at least 128, so its paid allowance has a ceiling independent of its possibly
conservative process centre bound or the spatial sampling mesh.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache

open Purelib
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

/-- The unchanged root process's nonnegative centre bound gives a uniform lower bound on its radius denominator. -/
private theorem denominator_lower {parameter : Canonical} (root : CertifiedSquareRoot.Certificate parameter) :
    Fraction.Cast.fromInt 128 ≤ CertifiedSquareRoot.Sampling.radiusDenominator root := by
  have coefficient : (64 : Fraction.Rational) * 2 = Fraction.Cast.fromInt 128 := by decide +kernel
  have oneLe : (1 : Fraction.Rational) ≤ 1 + root.value.name.process.centerBound :=
    Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
      root.value.name.process.centerBound_nonneg
  have positive : (0 : Fraction.Rational) < Fraction.Cast.fromInt (128 : Int) := by
    have original := Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide +kernel)
    rewrite [Fraction.Cast.natCast_eq_fromInt] at original
    exact original.trans_eq (by decide +kernel :
      Fraction.Cast.fromInt ((128 : Nat) : Int) = Fraction.Cast.fromInt (128 : Int))
  have lower := Arithmetic.mul_le_mul_of_nonneg_left_direct oneLe positive.le
  rewrite [Fraction.Field.mul_one_direct] at lower
  apply lower.trans_eq
  change Fraction.Cast.fromInt 128 * (1 + root.value.name.process.centerBound) =
    64 * (2 * (1 + root.value.name.process.centerBound))
  rewrite [← coefficient]
  exact Fraction.Field.mul_assoc _ _ _

/-- The same original paid radius denominator bounds the actual arithmetic allowance by one eighth of sensitivity. -/
theorem allowanceFactor_le_sensitivity {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (point : Canonical) (root : CertifiedSquareRoot.Certificate parameter) {floor : Fraction.Rational}
    (positive : 0 < floor) :
    allowanceFactor differential point root floor ≤ 1 + sensitivity differential point floor / 8 := by
  have denominatorPositive : (0 : Fraction.Rational) < Fraction.Cast.fromInt (128 : Int) := by
    have original := Fraction.Cast.Order.natCast_pos_direct (n := 128) (by decide +kernel)
    rewrite [Fraction.Cast.natCast_eq_fromInt] at original
    exact original.trans_eq (by decide +kernel :
      Fraction.Cast.fromInt ((128 : Nat) : Int) = Fraction.Cast.fromInt (128 : Int))
  have inverseBound := Fraction.Order.Field.inv_le_inv_of_pos_direct denominatorPositive (denominator_lower root)
  have numeratorNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 16) (sensitivity_nonnegative differential point positive)
  have fractionBound := Arithmetic.mul_le_mul_of_nonneg_left_direct inverseBound numeratorNonnegative
  have constants : (16 : Fraction.Rational) * (Fraction.Cast.fromInt 128)⁻¹ = (8 : Fraction.Rational)⁻¹ :=
    by decide +kernel
  unfold allowanceFactor
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  apply Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
  exact fractionBound.trans_eq (by
    calc
      _ = sensitivity differential point floor * ((16 : Fraction.Rational) * (Fraction.Cast.fromInt 128)⁻¹) := by ring1
      _ = _ := by rewrite [constants]; rfl)

/-- The original numerator box fold and actual candidate floor give a fixed arithmetic sensitivity ceiling. -/
@[expose] def sensitivityCeiling (differential : OddPowerDifferential radicand) (box : Box)
    (floor : Fraction.Rational) : Fraction.Rational :=
  Norm.Basic.normSq differential.scale * Bounds.Box.denseEvalNormBound differential.numerator box *
    Norm.Power.differenceFactor floor⁻¹ differential.denominatorExponent * (floor⁻¹ * floor⁻¹)

/-- The fixed arithmetic sensitivity ceiling is nonnegative under its original positive candidate floor. -/
theorem sensitivityCeiling_nonnegative (differential : OddPowerDifferential radicand) (box : Box)
    {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ sensitivityCeiling differential box floor := by
  have inverseNonnegative := (Fraction.Order.Field.inv_pos_direct positive).le
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg differential.scale)
        (Bounds.Box.denseHornerNormBounds_nonneg differential.numerator box).1)
      (Norm.Power.differenceFactor_nonnegative inverseNonnegative _))
    (Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative)

/-- The actual original arithmetic sensitivity obeys the fixed polynomial-box and observation-floor ceiling. -/
theorem sensitivity_le_ceiling (differential : OddPowerDifferential radicand) {box : Box} {point : Canonical}
    (inside : box.Contains point) {floor : Fraction.Rational} (positive : 0 < floor) :
    sensitivity differential point floor ≤ sensitivityCeiling differential box floor := by
  have inverseNonnegative := (Fraction.Order.Field.inv_pos_direct positive).le
  have numerator := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Bounds.Box.normSq_eval_le_denseEvalNormBound differential.numerator inside)
    (Norm.Basic.normSq_nonneg differential.scale)
  unfold sensitivity sensitivityCeiling
  rewrite [Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_right_direct numerator
      (Norm.Power.differenceFactor_nonnegative inverseNonnegative _))
    (Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative)

/-- The fixed-box paid arithmetic allowance ceiling uses the original one-eighth sensitivity reserve. -/
@[expose] def allowanceCeiling (differential : OddPowerDifferential radicand) (box : Box)
    (floor : Fraction.Rational) : Fraction.Rational :=
  1 + sensitivityCeiling differential box floor / 8

/-- The fixed-box arithmetic allowance ceiling is nonnegative under its actual candidate floor. -/
theorem allowanceCeiling_nonnegative (differential : OddPowerDifferential radicand) (box : Box)
    {floor : Fraction.Rational} (positive : 0 < floor) : 0 ≤ allowanceCeiling differential box floor :=
  Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
    (Fraction.Order.Field.div_nonneg_direct (sensitivityCeiling_nonnegative differential box positive)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 8))

/-- Every actual original observation allowance inside the fixed box obeys the same mesh-independent ceiling. -/
theorem allowanceFactor_le_ceiling {parameter : Canonical} (differential : OddPowerDifferential radicand)
    (root : CertifiedSquareRoot.Certificate parameter) {box : Box} {point : Canonical}
    (inside : box.Contains point) {floor : Fraction.Rational} (positive : 0 < floor) :
    allowanceFactor differential point root floor ≤ allowanceCeiling differential box floor := by
  apply (allowanceFactor_le_sensitivity differential point root positive).trans
  unfold allowanceCeiling
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  exact Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (sensitivity_le_ceiling differential inside positive)
      (Fraction.Order.Field.inv_pos_direct (by decide +kernel : (0 : Fraction.Rational) < 8)).le)

end Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache
