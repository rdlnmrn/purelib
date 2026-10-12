module
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Rounding.Floor

public import Purelib.Curves.Legendre.Acquisition.Gap
import Purelib.Data.Rat.Fraction.Compatibility
import Test.Curves.Legendre.SignedAcquisition
public import Test.Curves.Legendre.SignedGap
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-! # Regression clients through the public finite-acquisition interface -/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples

open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Examples
open Purelib
open Purelib.Data.Rat

/-- The retained signed-acquisition input for rational negative one. -/
abbrev negative :=
  Test.Curves.Legendre.SignedAcquisition.input (-1)
/-- The initial acquisition state of the negative input. -/
abbrev negativeStart := State.initial
  negative

/-- The actual signed-gap acquisition report for negative one.

Uses the certified unit gap at the original initial state and retains the resulting sign and work count. -/
def negativeSigned :=
  Curves.Legendre.Acquisition.Gap.signedGap negative
  negativeStart 1 (by decide)
  (Test.Curves.Legendre.SignedGap.negative_gap _)

/-- The retained signed acquisition reports the negative branch. -/
theorem signed_negative :
  negativeSigned.outcome.isPositive = false := by decide

/-- The retained signed acquisition count satisfies its logarithmic work bound.

Uses the exact ceiling and squared-gap constants of the original unit-gap request. -/
theorem signed_budget :
  negativeSigned.count ≤
    Nat.log2 (Rounding.Floor.ceilNat (1 / ((1 : Fraction.Rational) ^ 2 / 16))) + 2 :=
  (Curves.Legendre.Acquisition.Gap.signedGap_spec negative
    negativeStart 1 (by decide)
    (Test.Curves.Legendre.SignedGap.negative_gap _)).2.2.1

end Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples

end
