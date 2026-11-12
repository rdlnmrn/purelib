module

public import Purelib.Calculus.Jet.Quadratic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Tactic.Ring

/-! # Finite Taylor certificates on independently observed readings

An existing quadratic certificate can be transported to different displayed
base, output and slope readings. Each reading pays its own fourth-order
quadrance error. The original residual and the three reading discrepancies
give an explicit four-term remainder factor; no Taylor conclusion is assumed
for the new readings.
-/

public section

namespace Purelib.Calculus.Jet.Quadratic.Basic.Certificate

open Purelib.Data
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The difference of two displayed Gaussian readings obeys the existing two-leg squared-norm estimate. -/
private theorem subtraction_bound (first last : Canonical) :
    Norm.Basic.normSq (first - last) ≤ 2 * (Norm.Basic.normSq first + Norm.Basic.normSq last) := by
  have bound := Norm.Bounds.normSq_sub_le_via first 0 last
  rewrite [Gaussian.Basic.sub_zero, Gaussian.Basic.zero_sub, Norm.Basic.normSq_neg] at bound
  exact bound

/-- Bound the Taylor residual of independently observed base, output and slope readings.

The three nonnegative factors bound the actual discrepancies from the
original retained readings. A unit-quadrance increment bounds the extra
slope contribution, and the original Taylor residual remains one of the
four explicitly paid terms.
-/
theorem perturbation_bound {increment : Canonical} (certificate : Certificate increment)
    (base output slope : Canonical) (baseFactor outputFactor slopeFactor : Fraction.Rational)
    (unit : Norm.Basic.normSq increment ≤ 1)
    (baseBound : Norm.Basic.normSq (base - certificate.base) ≤ baseFactor * Norm.Basic.normSq increment ^ 2)
    (outputBound : Norm.Basic.normSq (output - certificate.output) ≤ outputFactor * Norm.Basic.normSq increment ^ 2)
    (slopeBound : Norm.Basic.normSq (slope - certificate.slope) ≤ slopeFactor * Norm.Basic.normSq increment ^ 2) :
    Norm.Basic.normSq (output - base - increment * slope) ≤
      4 * (certificate.factor + baseFactor + outputFactor + slopeFactor) * Norm.Basic.normSq increment ^ 2 := by
  let scale := Norm.Basic.normSq increment ^ 2
  let baseError := base - certificate.base
  let outputError := output - certificate.output
  let slopeError := slope - certificate.slope
  let remainder := output - base - increment * slope
  have slopeContribution : Norm.Basic.normSq (increment * slopeError) ≤ slopeFactor * scale := by
    rewrite [Norm.Basic.normSq_mul]
    calc
      _ ≤ 1 * Norm.Basic.normSq slopeError :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct unit (Norm.Basic.normSq_nonneg _)
      _ = Norm.Basic.normSq slopeError := Fraction.Field.one_mul _
      _ ≤ _ := slopeBound
  have originalBound : Norm.Basic.normSq certificate.remainder ≤ certificate.factor * scale := by
    change Norm.Basic.normSq certificate.remainder ≤ certificate.factor * Norm.Basic.normSq increment ^ 2
    rewrite [Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_eq_canonical]
    exact certificate.remainder_le
  have firstPair : Norm.Basic.normSq (outputError - baseError) ≤ 2 * (outputFactor + baseFactor) * scale :=
    calc
      _ ≤ 2 * (Norm.Basic.normSq outputError + Norm.Basic.normSq baseError) := subtraction_bound _ _
      _ ≤ 2 * (outputFactor * scale + baseFactor * scale) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct outputBound baseBound) (by decide +kernel)
      _ = _ := by ring1
  have secondPair : Norm.Basic.normSq (certificate.remainder - increment * slopeError) ≤
      2 * (certificate.factor + slopeFactor) * scale :=
    calc
      _ ≤ 2 * (Norm.Basic.normSq certificate.remainder + Norm.Basic.normSq (increment * slopeError)) :=
        subtraction_bound _ _
      _ ≤ 2 * (certificate.factor * scale + slopeFactor * scale) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct originalBound slopeContribution) (by decide +kernel)
      _ = _ := by ring1
  have identity : remainder = (outputError - baseError) + (certificate.remainder - increment * slopeError) := by
    rewrite [← certificate.expansion]
    unfold remainder outputError baseError slopeError
    ring1
  have remainderBound : Norm.Basic.normSq remainder ≤
      4 * (certificate.factor + baseFactor + outputFactor + slopeFactor) * scale := by
    rewrite [identity]
    calc
      _ ≤ 2 * (Norm.Basic.normSq (outputError - baseError) +
          Norm.Basic.normSq (certificate.remainder - increment * slopeError)) := Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 * (2 * (outputFactor + baseFactor) * scale +
          2 * (certificate.factor + slopeFactor) * scale) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Arithmetic.add_le_add_direct firstPair secondPair) (by decide +kernel)
      _ = _ := by ring1
  exact remainderBound

variable {increment : Canonical} (certificate : Certificate increment)
  (base output slope : Canonical) (baseFactor outputFactor slopeFactor : Fraction.Rational)
  (baseNonnegative : 0 ≤ baseFactor) (outputNonnegative : 0 ≤ outputFactor) (slopeNonnegative : 0 ≤ slopeFactor)
  (unit : Norm.Basic.normSq increment ≤ 1)
  (baseBound : Norm.Basic.normSq (base - certificate.base) ≤ baseFactor * Norm.Basic.normSq increment ^ 2)
  (outputBound : Norm.Basic.normSq (output - certificate.output) ≤ outputFactor * Norm.Basic.normSq increment ^ 2)
  (slopeBound : Norm.Basic.normSq (slope - certificate.slope) ≤ slopeFactor * Norm.Basic.normSq increment ^ 2)

include baseNonnegative outputNonnegative slopeNonnegative in
/-- The computed four-term transported remainder factor is nonnegative. -/
theorem perturbationFactor_nonnegative : 0 ≤ 4 * (certificate.factor + baseFactor + outputFactor + slopeFactor) :=
  Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.add_nonnegative
      (Fraction.Order.add_nonnegative
        (Fraction.Order.add_nonnegative certificate.factor_nonneg baseNonnegative) outputNonnegative)
      slopeNonnegative)

/-- Transport the original certificate to the independently observed readings with its computed remainder bound.

The constructor exposes only the retained readings and scalar factor. The
Taylor estimate and factor positivity are consumed through their opaque
mathematical certificates instead of exposing their proof implementations.
-/
@[expose] def perturb : Certificate increment where
  base := base
  output := output
  slope := slope
  remainder := output - base - increment * slope
  expansion := rfl
  factor := 4 * (certificate.factor + baseFactor + outputFactor + slopeFactor)
  factor_nonneg := perturbationFactor_nonnegative certificate baseFactor outputFactor slopeFactor
    baseNonnegative outputNonnegative slopeNonnegative
  remainder_le := by
    rewrite [← Norm.Basic.normSq_eq_canonical, ← Norm.Basic.normSq_eq_canonical]
    exact perturbation_bound certificate base output slope baseFactor outputFactor slopeFactor unit
      baseBound outputBound slopeBound

/-- The transported certificate retains the actual displayed base reading. -/
theorem perturb_base :
    (certificate.perturb base output slope baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative
      slopeNonnegative unit baseBound outputBound slopeBound).base = base := rfl

/-- The transported certificate retains the actual displayed output reading. -/
theorem perturb_output :
    (certificate.perturb base output slope baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative
      slopeNonnegative unit baseBound outputBound slopeBound).output = output := rfl

/-- The transported certificate retains the actual independently observed slope reading. -/
theorem perturb_slope :
    (certificate.perturb base output slope baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative
      slopeNonnegative unit baseBound outputBound slopeBound).slope = slope := rfl

/-- The transported certificate has exactly the computed four-term finite remainder factor. -/
theorem perturb_factor :
    (certificate.perturb base output slope baseFactor outputFactor slopeFactor baseNonnegative outputNonnegative
      slopeNonnegative unit baseBound outputBound slopeBound).factor =
      4 * (certificate.factor + baseFactor + outputFactor + slopeFactor) := rfl

end Purelib.Calculus.Jet.Quadratic.Basic.Certificate
