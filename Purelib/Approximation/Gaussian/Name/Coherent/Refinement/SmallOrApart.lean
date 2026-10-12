module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Name.Coherent
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
public import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
public import Purelib.Approximation.Rational.Request.Sixth
import Init.Core
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement (State)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Enclosure

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Approximation.Gaussian.Process.Apart

open Purelib.Approximation.Rational

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Requested-precision denominator acquisition

One prescribed source refinement followed by the audited small-or-apart
decision returns either candidate apartness or a persistent squared-norm
upper bound. Smallness is relative to a supplied threshold, not a zero test.
The ordinary canonical retry index is preserved: this is a requested-target
refinement, not a falsely labelled canonical `Progress` transition.
-/

namespace Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart

set_option genInjectivity false in
/-- Both outcomes share the exact cached inspection; only the successful branch carries candidate apartness. There is no
unresolved outcome. -/
structure Report (denominator :
  Coherent.CoherentNamed) (start : State denominator)
    (threshold : Fraction.Rational) (positive : 0 < threshold) where
  /-- The exact cached denominator inspection at one sixth of the displayed positive threshold. -/ inspection :
    Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator start (threshold / 6)
        (Request.Sixth.requestTarget_positive positive)
  /-- Either candidate apartness or a persistent strict candidate bound at the exact retained inspection state. -/
    outcome : Sum
    (Possible.PossibleApart (Gaussian.Process.Based.based denominator.name.process inspection.retained.source))
    (Approximation.Gaussian.Name.Coherent.Refinement.Small denominator inspection.retained threshold)
  /-- Selecting the small branch retains its whole-ball certificate for the original cached enclosure. -/ small_ball : ∀
    certificate, outcome = .inr certificate →
    Residual.SmallBall inspection.ball threshold

constructive_injectivity Report

/-- Consume an already cached fine inspection without another refinement. -/
def classify {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator start (threshold / 6)
        (Request.Sixth.requestTarget_positive
      positive)) :
    Report denominator start threshold positive :=
  { inspection := inspection
    outcome := match Residual.decide inspection.ball threshold positive
        inspection.accurate with
      | .small certificate => .inr
          { bound := by
              intro value possible
              apply Residual.normSq_lt_of_contains certificate
              rw [inspection.ball_eq]
              exact denominator.name.process.possible_inside possible }
      | .apart certificate => .inl (inspection.evidence certificate)
    small_ball := by
      intro small equal
      cases decision : Residual.decide inspection.ball threshold positive
          inspection.accurate with
      | small certificate => exact certificate
      | apart certificate =>
          rw [decision] at equal
          cases equal }

/-- The inspected ball retains its original whole-ball certificate. Only the separately stored candidate bound is
propagated to later sources; their displayed balls need not be nested inside this one. -/
theorem Report.small_bound {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    {threshold : Fraction.Rational} {positive : 0 < threshold}
    (report : Report denominator start threshold positive)
    {certificate : Approximation.Gaussian.Name.Coherent.Refinement.Small denominator report.inspection.retained
        threshold}
    (selected : report.outcome = .inr certificate)
    {value : Data.Gaussian.Basic.Canonical} (inside : report.inspection.ball.Contains value) :
      Data.Gaussian.Norm.Basic.normSq value < threshold :=
  Residual.normSq_lt_of_contains (report.small_ball certificate selected) inside

/-- One prescribed refinement, then one finite rational decision. This counts refinement calls, not the runtime of the
underlying evaluator. -/
def acquire {denominator :
  Coherent.CoherentNamed} (start : State denominator)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
      Report denominator start threshold positive :=
  classify threshold positive (Inspection.request start
    (threshold / 6) (Request.Sixth.requestTarget_positive positive))

/-- A small cached inspection selects the branch carrying a persistent candidate-smallness certificate. -/
theorem classify_small {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator start (threshold / 6)
        (Request.Sixth.requestTarget_positive
      positive))
    (small : Residual.SmallBall inspection.ball threshold) :
    ∃ certificate, (classify threshold positive
      inspection).outcome = .inr certificate := by
  unfold classify
  dsimp only
  rw [Residual.decide, dif_pos small]
  exact ⟨_, rfl⟩

/-- A cached inspection that fails the smallness predicate selects the branch carrying candidate apartness. -/
theorem classify_apart {denominator :
  Coherent.CoherentNamed} {start : State denominator}
    (threshold : Fraction.Rational) (positive : 0 < threshold)
    (inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection denominator start (threshold / 6)
        (Request.Sixth.requestTarget_positive
      positive))
    (notSmall : ¬ Residual.SmallBall inspection.ball threshold) :
    ∃ evidence, (classify threshold positive
      inspection).outcome = .inl evidence := by
  unfold classify
  dsimp only
  rw [Residual.decide, dif_neg notSmall]
  exact ⟨_, rfl⟩

/-- Acquisition retains exactly the source produced by refining at one sixth of the threshold. -/
@[simp] theorem acquire_source {denominator
  : Coherent.CoherentNamed} (start : State denominator)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
    (acquire start threshold
      positive).inspection.retained.source =
      denominator.name.process.refine start.source (threshold / 6)
        (Request.Sixth.requestTarget_positive positive) := rfl

/-- Requested-threshold acquisition preserves the canonical retry index. -/
@[simp] theorem acquire_nextIndex
  {denominator : Coherent.CoherentNamed} (start : State denominator)
    (threshold : Fraction.Rational) (positive : 0 < threshold) :
    (acquire start threshold
      positive).inspection.retained.nextIndex = start.nextIndex := rfl
end Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart

end
