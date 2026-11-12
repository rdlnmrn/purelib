module
public import Purelib.Examples.Approximation.Gaussian.Process.Imaginary.DelayedUnit
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Basic
import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Acquisition.State
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Rounding.Floor

public import Purelib.Curves.Legendre.Acquisition.Gap
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Canonical
import Purelib.Approximation.Gaussian.Acquisition.Signed.Gap.Decision
import Purelib.Approximation.Gaussian.Name.Coherent

@[expose] public section

/-!
Exact imaginary inputs, certified sign gaps and a signed acquisition report.
-/

namespace Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples

open Purelib.Approximation.Gaussian.Acquisition
open Purelib.Examples
open Purelib
open Purelib.Data.Rat

open Purelib.Examples.Approximation.Gaussian.Process.Imaginary
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Approximation.Gaussian.Acquisition.Signed (Gap)
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Name

/-- The exact coherent Gaussian name with zero real coordinate and the supplied imaginary height. -/
def input (height : Fraction.Rational) :
    Coherent.CoherentNamed :=
  Coherence.exact ⟨0, height⟩

/-- The exact positive unit input has the retained signed gap one. -/
theorem positive_gap (state : State (input 1))
    : Gap
  (input 1) state 1 := by
  intro value possible
  change value = (⟨0, 1⟩ : Gaussian) at possible
  subst value
  exact .inr (by decide)

/-- The exact negative unit input has the retained signed gap one. -/
theorem negative_gap (state : State (input
    (-1))) : Gap
  (input (-1)) state 1 := by
  intro value possible
  change value = (⟨0, -1⟩ : Gaussian) at possible
  subst value
  exact .inl (by decide)

/-- The delayed imaginary-unit input has the retained signed gap one. -/
theorem delayed_gap (state : State DelayedUnit.name) :
    Gap
  DelayedUnit.name state 1 := by
  intro value possible
  change value = DelayedUnit.value at possible
  subst value
  exact .inr (by decide)

/-- The retained signed-acquisition input for rational negative one. -/
abbrev negative :=
  input (-1)
/-- The initial acquisition state of the negative input. -/
abbrev negativeStart := State.initial
  negative

/-- The actual signed-gap acquisition report for negative one.

Uses the certified unit gap at the original initial state and retains the resulting sign and work count. -/
def negativeSigned :=
  Curves.Legendre.Acquisition.Gap.signedGap negative
  negativeStart 1 (by decide)
  (negative_gap _)

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
    (negative_gap _)).2.2.1

end Purelib.Examples.Approximation.Gaussian.Acquisition.Signed.WorkedExamples

end
