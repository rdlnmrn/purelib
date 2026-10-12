module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
public import Purelib.Approximation.Gaussian.Enclosure.Ball.WeightedBound
public import Purelib.Approximation.Gaussian.Logarithm.Chart.Enclosure
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Enclosure.Ball

open Purelib.Approximation.Gaussian.Logarithm.Chart

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Decidable finite safety for anchored complex-log charts

For a rational chart factor and one displayed rational input ball, this module
computes conservative numerator and denominator balls for

`factor * z - 1` and `factor * z + 1`.

The denominator ball must pass the existing square-root-free centre-separation
test.  Dividing the two finite balls by that certificate must then pass an
indexed weighted norm bound strictly below `1/9`.  The weight increases along
the intended refinement schedule: its centre coefficient approaches one while
the shrinking enclosure error is still paid explicitly.  These exact rational
checks imply the target-side fields of `SafeOverlapExtension` after rebasing
the target process to the tested state.

Failure is deliberately only failure of this sufficient finite test.  It is
not evidence that no logarithm chart exists.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Chart.Safety

/-- Exact rational sufficient test for the reduced quotient ball at one weight/refinement index. -/
def ReducedSmall {factor : Canonical}
  {input : Ball}
    (separated : Enclosure.DenominatorSeparated factor input) (index : Nat) : Prop :=
  WeightedBound.weightedUpper index (Enclosure.reducedBall separated) < 1 / 9

/-- Decide the weighted reduced-ball test by exact rational comparison. -/
instance reducedSmallDecidable {factor :
  Canonical} {input : Ball}
    (separated : Enclosure.DenominatorSeparated factor input) (index : Nat) :
    Decidable (ReducedSmall separated index) := by
  unfold ReducedSmall
    Ball.WeightedBound.weightedUpper
  infer_instance

/-- Both rational conditions needed to build a safe chart on the refinement future of the displayed ball. -/
structure Certificate (factor :
  Canonical) (input : Ball) (index : Nat) : Prop where
  /-- The transformed denominator ball passes its whole-ball separation test. -/ denominatorSeparated :
    Enclosure.DenominatorSeparated factor input
  /-- Using that same separation certificate, the reduced ball meets the indexed strict one-ninth weighted bound. -/
    reducedSmall : ReducedSmall denominatorSeparated index

/-- Decide both dependent chart safety conditions, retaining the original denominator-separation evidence on success. -/
instance certificateDecidable (factor :
  Canonical) (input : Ball)
    (index : Nat) : Decidable (Certificate factor input index) := by
  by_cases separated : Enclosure.DenominatorSeparated factor input
  · by_cases small : ReducedSmall separated index
    · exact isTrue
        { denominatorSeparated := separated
          reducedSmall := small }
    · exact isFalse (fun certificate => small certificate.reducedSmall)
  · exact isFalse (fun certificate =>
      separated certificate.denominatorSeparated)

namespace Certificate

/-- The lower norm-square retained by the denominator certificate. -/
def lowerSq {factor :
  Canonical} {input : Ball}
    {index : Nat} (certificate : Approximation.Gaussian.Logarithm.Chart.Safety.Certificate factor input index) :
      Fraction.Rational :=
  (Enclosure.denominatorApart certificate.denominatorSeparated).lowerSq

/-- The lower quadrance retained by the chart denominator certificate is strictly positive. -/
theorem lowerSq_positive {factor :
  Canonical} {input : Ball}
    {index : Nat} (certificate : Approximation.Gaussian.Logarithm.Chart.Safety.Certificate factor input index) :
    0 < certificate.lowerSq :=
  (Enclosure.denominatorApart certificate.denominatorSeparated).positive

/-- Every point in the tested input ball has a uniformly separated chart denominator. -/
theorem denominator_lower {factor value :
  Canonical} {input : Ball}
    {index : Nat} (certificate : Approximation.Gaussian.Logarithm.Chart.Safety.Certificate factor input index)
    (inside : input.Contains value) :
    certificate.lowerSq ≤ Data.Gaussian.Norm.Basic.normSq (factor * value + 1) :=
  (Enclosure.denominatorApart certificate.denominatorSeparated).lower
    (Enclosure.denominatorBall_contains inside)

/-- The reduced chart argument formed from any two independently admitted input candidates lies in the required local
logarithm disk. -/
theorem reduced_bound {factor numerator
  denominator : Canonical} {input : Ball}
    {index : Nat} (certificate : Approximation.Gaussian.Logarithm.Chart.Safety.Certificate factor input index)
    (numeratorInside : input.Contains numerator)
    (denominatorInside : input.Contains denominator) :
    Data.Gaussian.Norm.Basic.normSq
        ((factor * numerator - 1) / (factor * denominator + 1)) ≤ 1 / 9 := by
  have inside :
      (Enclosure.reducedBall certificate.denominatorSeparated).Contains
        ((factor * numerator - 1) / (factor * denominator + 1)) :=
    Ball.contains_div
      (Enclosure.denominatorApart certificate.denominatorSeparated)
      (Enclosure.numeratorBall_contains numeratorInside)
      (Enclosure.denominatorBall_contains denominatorInside)
  exact (WeightedBound.normSq_lt_of_weightedUpper certificate.reducedSmall inside).le

end Certificate
end Purelib.Approximation.Gaussian.Logarithm.Chart.Safety

end
