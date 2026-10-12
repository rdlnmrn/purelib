module
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Gap
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples
import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne
public import Purelib.Examples.Approximation.Gaussian.Division.Partial.ZeroObstruction
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

@[expose] public section

namespace Purelib.Examples.Approximation.Gaussian.Division.Gap.WorkedExamples

open Purelib.Approximation.Gaussian.Name.Coherent

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)
open Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples (zeroInput oneInput tinyInput tinyValue
  tiny_nonzero)
open Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne (delayedOne)
open Purelib.Data.Gaussian
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

/-- The squared norm of the fixed nonzero Gaussian rational one tenth. -/
def tinyGap :=
  Data.Gaussian.Norm.Basic.normSq
  Bounded.WorkedExamples.tinyValue

/-- The fixed tiny-input squared-norm gap is positive. -/
theorem tinyGap_positive : 0 <
  tinyGap :=
  Norm.Basic.normSq_pos Bounded.WorkedExamples.tiny_nonzero

/-- The exact zero input satisfies the zero branch of a unit gap. -/
theorem zero_gap :
    Refinement.Gap
  Bounded.WorkedExamples.zeroInput (Refinement.State.initial
      Bounded.WorkedExamples.zeroInput) 1 :=
  fun possible => .inl possible

/-- The exact one input satisfies the nonzero branch of a unit gap. -/
theorem one_gap :
    Refinement.Gap
  Bounded.WorkedExamples.oneInput (Refinement.State.initial
      Bounded.WorkedExamples.oneInput) 1 := by
  intro value possible
  change value = 1 at possible
  subst value
  exact .inr (by decide)

/-- The exact tiny input satisfies its retained squared-norm gap. -/
theorem tiny_gap :
    Refinement.Gap
  Bounded.WorkedExamples.tinyInput (Refinement.State.initial
      Bounded.WorkedExamples.tinyInput) tinyGap :=
  by
  intro value possible
  change value = Bounded.WorkedExamples.tinyValue at possible
  subst value
  exact .inr le_rfl

/-- The delayed name of one satisfies a unit gap at its initial state.

Its possible value is exactly one even though the initial enclosing ball contains zero. -/
theorem delayed_gap :
    Refinement.Gap
  Partial.DelayedOne.delayedOne (Refinement.State.initial
      Partial.DelayedOne.delayedOne) 1 := by
  intro value possible
  change value = 1 at possible
  subst value
  exact .inr (by decide)

/-- Gap acquisition at exact zero returns the zero outcome. -/
theorem zero_excluded :
    (GapDecision.acquire (Refinement.State.initial
        Bounded.WorkedExamples.zeroInput) 1 (by decide)
      zero_gap).2.isPrepared = false := by decide

/-- Gap acquisition at exact one returns a prepared denominator. -/
theorem one_prepared :
    (GapDecision.acquire (Refinement.State.initial Bounded.WorkedExamples.oneInput)
        1 (by decide)
      one_gap).2.isPrepared = true := by decide

/-- Gap acquisition prepares the tiny input at its certified positive gap. -/
theorem tiny_prepared :
    (GapDecision.acquire (Refinement.State.initial
        Bounded.WorkedExamples.tinyInput) tinyGap
      tinyGap_positive tiny_gap).2.isPrepared = true := by
  have prepared : ∃ evidence,
      (SmallOrApart.acquire (Refinement.State.initial
          Bounded.WorkedExamples.tinyInput)
        tinyGap tinyGap_positive).outcome = .inl evidence := by
    apply SmallOrApart.classify_apart
    change ¬ 2 * (0 + tinyGap) < tinyGap
    have lower : tinyGap ≤ 2 * (0 + tinyGap) := by
      calc
        tinyGap ≤ tinyGap + tinyGap := le_add_of_nonneg_left
          tinyGap_positive.le
        _ = 2 * (0 + tinyGap) := by ring1
    exact not_lt_of_ge lower
  obtain ⟨evidence, equal⟩ := prepared
  unfold GapDecision.acquire
  dsimp only
  rw [equal]
  rfl

/-- The retained gap prepares the delayed denominator after acquisition. -/
theorem delayed_prepared :
    (GapDecision.acquire (Refinement.State.initial Partial.DelayedOne.delayedOne) 1
        (by decide)
      delayed_gap).2.isPrepared = true := by decide

/-- Every padded-zero state satisfies the zero branch of a unit gap. -/
theorem padded_gap (state :
    Refinement.State
  Partial.ZeroObstruction.paddedZero) : Refinement.Gap
      Partial.ZeroObstruction.paddedZero state 1 :=
  fun possible => .inl possible

/-- Gap acquisition at padded zero returns the zero outcome. -/
theorem padded_zero_excluded :
    (GapDecision.acquire (Refinement.State.initial
        Partial.ZeroObstruction.paddedZero) 1 (by decide)
      (padded_gap _)).2.isPrepared = false := by decide

end Purelib.Examples.Approximation.Gaussian.Division.Gap.WorkedExamples

end
