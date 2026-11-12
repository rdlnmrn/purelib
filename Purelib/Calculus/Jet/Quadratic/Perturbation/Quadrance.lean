module

public import Purelib.Calculus.Jet.Quadratic.Perturbation
public import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Stronger quadrance estimates on unchanged Taylor certificates

A separate proved bound on the same original remainder can be used without
changing the certificate's recorded factor or any retained reading. Three
actual independently paid reading discrepancies and a nonzero increment
give quantitative perturbation and divided-difference estimates directly.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction

/-- Three actual reading payments compose with a separate bound on the original unchanged remainder.

The displayed factor bounds that same remainder, rather than the record's
factor field. The exact original expansion identifies the four actual
terms. No replacement certificate or relation between factor fields is
constructed, including when a displayed payment factor is zero.
-/
theorem perturbation_bound_of_remainder_le {increment : Canonical} (certificate : Certificate increment)
    (base output slope : Canonical) (remainderFactor baseFactor outputFactor slopeFactor : Rational)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (originalBound : Norm.Basic.normSq certificate.remainder ≤ remainderFactor * Norm.Basic.normSq increment ^ 2)
    (baseBound : Norm.Basic.normSq (base - certificate.base) ≤ baseFactor * Norm.Basic.normSq increment ^ 2)
    (outputBound : Norm.Basic.normSq (output - certificate.output) ≤ outputFactor * Norm.Basic.normSq increment ^ 2)
    (slopeBound : Norm.Basic.normSq (slope - certificate.slope) ≤ slopeFactor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (output - base - increment * slope) ≤
      4 * (remainderFactor + baseFactor + outputFactor + slopeFactor) * Norm.Basic.normSq increment ^ 2 := by
  let scale := Norm.Basic.normSq increment ^ 2
  let baseError := base - certificate.base
  let outputError := output - certificate.output
  let slopeError := slope - certificate.slope
  have slopeContribution : Norm.Basic.normSq (increment * slopeError) ≤ slopeFactor * scale := by
    rewrite [Norm.Basic.normSq_mul]
    exact ((Order.Arithmetic.mul_le_mul_of_nonneg_right_direct unit (Norm.Basic.normSq_nonneg _)).trans_eq
      (Field.one_mul _)).trans slopeBound
  have firstPair : Norm.Basic.normSq (outputError - baseError) ≤ 2 * (outputFactor + baseFactor) * scale :=
    (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct outputBound baseBound) (by decide +kernel)).trans_eq (by ring1))
  have secondPair : Norm.Basic.normSq (certificate.remainder - increment * slopeError) ≤
      2 * (remainderFactor + slopeFactor) * scale :=
    (Norm.Bounds.normSq_sub_le_two _ _).trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct originalBound slopeContribution) (by decide +kernel)).trans_eq
          (by ring1))
  have identity : output - base - increment * slope =
      (outputError - baseError) + (certificate.remainder - increment * slopeError) := by
    rewrite [← certificate.expansion]
    dsimp only [outputError, baseError, slopeError]
    ring1
  exact (congrArg Norm.Basic.normSq identity).trans_le
    ((Norm.Bounds.normSq_add_le_two _ _).trans
      ((Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Order.Arithmetic.add_le_add_direct firstPair secondPair) (by decide +kernel)).trans_eq (by ring1)))

/-- A stronger bound on the same original remainder gives its literal divided-difference estimate.

Only the original expansion, its actual nonzero increment and the separate
proved remainder payment are used. The stored base/output/slope/remainder
and recorded factor remain unchanged.
-/
theorem differenceQuotient_le_of_remainder_le {increment : Canonical} (certificate : Certificate increment)
    (nonzero : increment ≠ 0) (factor : Rational)
    (bounded : Norm.Basic.normSq certificate.remainder ≤ factor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq ((certificate.output - certificate.base) / increment - certificate.slope) ≤
      factor * Norm.Basic.normSq increment := by
  have numerator : increment *
      ((certificate.output - certificate.base) / increment - certificate.slope) = certificate.remainder := by
    change increment * ((certificate.output - certificate.base) * increment⁻¹ - certificate.slope) = _
    calc
      _ = (increment * increment⁻¹) * (certificate.output - certificate.base) -
          increment * certificate.slope := by ring1
      _ = certificate.output - certificate.base - increment * certificate.slope := by
        rewrite [Canonical.mul_inv_cancel increment nonzero, Canonical.one_mul]
        rfl
      _ = _ := certificate.expansion
  have scaled := (congrArg Norm.Basic.normSq numerator).trans_le bounded
  rewrite [Norm.Basic.normSq_mul] at scaled
  have multiplied :
      Norm.Basic.normSq ((certificate.output - certificate.base) / increment - certificate.slope) *
          Norm.Basic.normSq increment ≤
        (factor * Norm.Basic.normSq increment) * Norm.Basic.normSq increment :=
    (Field.mul_comm _ _).trans_le (scaled.trans_eq (by ring1))
  exact Order.Arithmetic.le_of_mul_le_mul_right_direct multiplied (Norm.Basic.normSq_pos nonzero)

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate

end
