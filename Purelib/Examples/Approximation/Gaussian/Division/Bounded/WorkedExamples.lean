module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Division.Partial.Bounded
import Purelib.Approximation.Gaussian.Division.Partial.Step
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Examples.Approximation.Gaussian.Division.Partial.DelayedOne
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Division.Partial.Requirement
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Ready

@[expose] public section

/-!
# Finite small-or-prepared regression clients

These examples exercise actual decision outcomes, including a nonzero small
input. They do not identify smallness with zero or evaluate generated period
coefficient banks.
-/

namespace Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Approximation.Gaussian.Name.Coherent
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)

open Purelib.Approximation.Gaussian.Name
open Purelib.Data.Gaussian
open Purelib.Examples.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Name.Coherent.Refinement
open Purelib.Data.Rat
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Division
open Purelib.Approximation.Gaussian.Process

/-- The exact coherent Gaussian name of zero. -/
def zeroInput : CoherentNamed :=
  CoherentNamed.Coherence.exact 0
/-- The exact coherent Gaussian name of one. -/
def oneInput : CoherentNamed :=
  CoherentNamed.Coherence.exact 1

/-- The nonzero Gaussian rational (1/10,0). -/
def tinyValue : Basic.Canonical := ⟨1 /
  10, 0⟩
/-- The exact coherent name of the fixed small Gaussian rational. -/
def tinyInput : CoherentNamed :=
  CoherentNamed.Coherence.exact tinyValue

/-- The fixed Gaussian rational one tenth is nonzero. -/
theorem tiny_nonzero :
  tinyValue ≠ 0 := by decide

/-- Every positive threshold classifies the exact zero name as small.

Returns the classifier's actual smallness certificate for the original initial inspection. -/
theorem zero_small (threshold :
  Rational) (positive : 0 < threshold) :
    ∃ certificate,
      (SmallOrApart.acquire (Refinement.State.initial
          zeroInput)
        threshold positive).outcome = .inr certificate := by
  apply SmallOrApart.classify_small
  change (2 : Rational) * (0 + Norm.Basic.normSq 0) < threshold
  simpa only [Norm.Basic.normSq_zero, _root_.add_zero,
    MulZeroClass.mul_zero] using positive

/-- The exact name of one is prepared at threshold one. -/
theorem one_prepared :
    ∃ evidence,
      (SmallOrApart.acquire (Refinement.State.initial
          oneInput)
        1 (by decide)).outcome = .inl evidence := by
  apply SmallOrApart.classify_apart
  decide

/-- The exact name of one tenth is small at threshold one. -/
theorem tiny_small :
    ∃ certificate,
      (SmallOrApart.acquire (Refinement.State.initial
          tinyInput)
        1 (by decide)).outcome = .inr certificate := by
  apply SmallOrApart.classify_small
  decide

/-- The delayed name of one is prepared by the bounded inspection. -/
theorem delayed_prepared :
    ∃ evidence,
      (SmallOrApart.acquire (Refinement.State.initial
          Partial.DelayedOne.delayedOne)
        1 (by decide)).outcome = .inl evidence := by
  apply SmallOrApart.classify_apart
  decide

/-- The delayed denominator inspection retains its refined Boolean source. -/
theorem delayed_source_refined :
    (SmallOrApart.acquire (Refinement.State.initial Partial.DelayedOne.delayedOne)
      1 (by decide)).inspection.retained.source = true := rfl

/-- The bounded inspection retains the original next-index counter. -/
theorem delayed_index_unchanged :
    (SmallOrApart.acquire (Refinement.State.initial Partial.DelayedOne.delayedOne)
      1 (by decide)).inspection.retained.nextIndex = 0 := rfl

/-- A prepared delayed denominator yields a bounded quotient result.

Uses the original classification outcome to retain the quotient for any supplied coherent numerator. -/
theorem delayed_division_ready (numerator
  : CoherentNamed) :
    ∃ result,
      (SmallOrApart.acquire (Refinement.State.initial
          Partial.DelayedOne.delayedOne)
        1 (by decide)).divide numerator = .inl result := by
  obtain ⟨evidence, equal⟩ := delayed_prepared
  unfold SmallOrApart.Report.divide
  rw [equal]
  exact ⟨_, rfl⟩

/-- Division at threshold one retains the small-denominator certificate. -/
theorem tiny_division_small (numerator :
  CoherentNamed) :
    ∃ certificate,
      (SmallOrApart.acquire (Refinement.State.initial
          tinyInput)
        1 (by decide)).divide numerator = .inr certificate := by
  obtain ⟨certificate, equal⟩ := tiny_small
  unfold SmallOrApart.Report.divide
  rw [equal]
  exact ⟨_, rfl⟩

/-- Every point in the retained tiny-input ball has squared norm below one.

Uses the actual selected smallness certificate, rather than only the ball center. -/
theorem tiny_whole_ball {value :
  Basic.Canonical}
    (inside : (SmallOrApart.acquire (Refinement.State.initial
        tinyInput)
      1 (by decide)).inspection.ball.Contains value) :
    Norm.Basic.normSq value < 1 := by
  obtain ⟨certificate, selected⟩ := tiny_small
  exact SmallOrApart.Report.small_bound _ selected inside

/-- Manual apartness-based resumption agrees with a retained bounded quotient.

Returns the actual resumed output and readiness evidence with an explicit equivalence witness to the original result's
name. -/
theorem manual_route_compatible
  {numerator denominator : CoherentNamed}
    {first : Refinement.State denominator}
    (result : Partial.Bounded.Quotient numerator denominator first)
    (other : Refinement.State denominator)
    (evidence : Apart.Possible.PossibleApart (Based.based denominator.name.process other.source)) :
    ∃ output valid,
      Partial.Step.resume numerator denominator other
        .candidateApartness evidence = .ready output valid ∧
      Nonempty (Equivalence.NamedEquivalent result.output.name output.name) := by
  obtain ⟨output, valid, equal⟩ := Partial.Step.resume_is_ready
    numerator denominator other .candidateApartness evidence
  exact ⟨output, valid, equal, ⟨result.respects valid⟩⟩

/-- A separated automatic division step agrees with a retained bounded quotient.

The supplied ball-separation inequality yields the actual ready output and its equivalence to the original quotient. -/
theorem automatic_route_compatible
  {numerator denominator : CoherentNamed}
    {first : Refinement.State denominator}
    (result : Partial.Bounded.Quotient numerator denominator first)
    (other : Refinement.State denominator)
    (separated : 2 * (denominator.name.process.ball other.source).radiusSq <
      Norm.Basic.normSq
        (denominator.name.process.ball other.source).center) :
    ∃ output valid,
      Partial.Step.step numerator denominator other = .ready output valid ∧
      Nonempty (Equivalence.NamedEquivalent result.output.name output.name) := by
  obtain ⟨output, valid, equal⟩ := Partial.Step.step_is_ready_of_separated
    numerator denominator other separated
  exact ⟨output, valid, equal, ⟨result.respects valid⟩⟩

end Purelib.Examples.Approximation.Gaussian.Division.Bounded.WorkedExamples

end
