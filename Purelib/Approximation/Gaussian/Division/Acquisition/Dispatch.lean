module
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Division.Prepared.FromEvidence
import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.SmallOrApart
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Annotated.Arithmetic
import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.Division.Acquisition.Report
import Purelib.Approximation.Gaussian.Division.Acquisition.State
import Purelib.Approximation.Gaussian.Division.Bounded.Certificate
import Purelib.Approximation.Gaussian.Division.Gap
import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Division.Search.State
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.GapDecision
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order
import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Division.Prepared.Basic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Enclosure.Residual
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Small
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic
import Purelib.Approximation.Rational.Request.Sixth
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Acquisition (Annotated)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Division.Acquisition

open Purelib.Approximation.Gaussian.Division.Acquisition.State

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.Rat

section
@[expose] public section

/-!
# Evidence-directed division with reusable state

The dispatcher first reuses an exact decision, then tries inferred finite
provenance, then an optional proved candidate gap, and finally one bounded
numerical request. A small result is inconclusive, not zero. Gap exclusion
is explicitly scoped to the retained branch. Exact provenance concerns
operational identities and is never used as a pointwise candidate gap.

All routes return the retained state. Requested refinements preserve the
retry index and transport optional gap evidence. Exact decisions, including
negative ones, are cached for subsequent numerators and requests.
-/

namespace Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Division (Prepared)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Cache the retained exact denominator decision and return its prepared quotient or operational-zero obstruction. -/
def fromDecision {channel : Coherent.CoherentNamed}
  {input : State.Input channel} (numerator : Coherent.CoherentNamed)
    (threshold : Fraction.Rational) (step : State.Step input) (decision :
        Approximation.Gaussian.Division.Prepared.Decision channel) : Approximation.Gaussian.Division.Acquisition.Report
      numerator input threshold :=
  ⟨step.cache decision, match decision with
    | .prepared prepared => .ready (Quotient.quotient numerator prepared)
    | .excluded zero => .zero zero⟩

/-- Acquire division evidence while reusing the original denominator state and any cached decision.

The dispatcher tries cached evidence, supported provenance, a retained candidate gap, and one numerical inspection in
that order; smallness remains inconclusive. -/
def acquire (numerator : Coherent.CoherentNamed)
  {channel : Coherent.CoherentNamed} (input : State.Input channel)
    (threshold : Fraction.Rational) (positive : 0 < threshold) : Approximation.Gaussian.Division.Acquisition.Report
        numerator input threshold :=
  match input.cached with
  | some decision => fromDecision numerator threshold
    (Step.unchanged input .cached) decision
  | none => match input.provenance with
    | some provenance => fromDecision numerator threshold
      (Step.unchanged input .symbolic)
        (Provenance.exact provenance)
    | none => match input.gap with
      | some gap =>
          let report := GapDecision.acquire input.state gap.gap gap.positive gap.certificate
          let step := Step.inspected input .gap report.1
          match report.2 with
          | .prepared evidence => fromDecision numerator threshold
            step
              (.prepared (Prepared.ofEvidence report.1.retained evidence))
          | .excluded zero => ⟨step, .branchZero zero⟩
      | none =>
          let report := SmallOrApart.acquire input.state threshold positive
          let step := Step.inspected input .numerical report.inspection
          match selected : report.outcome with
          | .inl evidence => fromDecision numerator threshold step
              (.prepared (Prepared.ofEvidence report.inspection.retained evidence))
          | .inr small => ⟨step, .small
              ⟨report.inspection.ball, report.inspection.ball_eq, report.small_ball small selected, small⟩⟩

/-- Continue acquisition from the report's exact retained input for a new numerator and positive threshold. -/
def Report.resume {numerator channel :
  Coherent.CoherentNamed} {input : State.Input channel} {threshold : Fraction.Rational}
    (report : Approximation.Gaussian.Division.Acquisition.Report numerator input threshold) (nextNumerator :
        Coherent.CoherentNamed)
    (nextThreshold : Fraction.Rational) (positive : 0 < nextThreshold) :
        Approximation.Gaussian.Division.Acquisition.Report nextNumerator report.1.next
      nextThreshold :=
  acquire nextNumerator report.1.next nextThreshold positive

/-- An available cached decision is reused without changing the denominator's retained refinement state. -/
theorem acquire_cached (numerator :
  Coherent.CoherentNamed) {channel : Coherent.CoherentNamed} (input : State.Input channel)
    (threshold : Fraction.Rational) (positive : 0 < threshold) (decision :
        Approximation.Gaussian.Division.Prepared.Decision channel)
    (cached : input.cached = some decision) :
    (acquire numerator input threshold positive).1.route =
      .cached ∧
    (acquire numerator input threshold
      positive).1.next.state = input.state := by
  unfold acquire
  rw [cached]
  exact ⟨rfl, rfl⟩

/-- Supported provenance always resolves the exact operational question; the small and branch-only outcomes cannot occur
on this route. -/
theorem acquire_symbolic_decisive (numerator :
  Coherent.CoherentNamed) {channel : Coherent.CoherentNamed}
    (input : State.Input channel) (threshold : Fraction.Rational) (positive : 0 < threshold)
    (provenance : Approximation.Gaussian.Acquisition.Provenance channel) (uncached : input.cached = none)
    (inferred : input.provenance = some provenance) :
    (acquire numerator input threshold positive).2.status =
      .ready ∨
    (acquire numerator input threshold positive).2.status =
      .zero := by
  unfold acquire
  rw [uncached, inferred]
  dsimp only
  unfold fromDecision
  dsimp only
  cases Provenance.exact provenance with
  | prepared prepared => exact .inl rfl
  | excluded zero => exact .inr rfl

/-- A computed zero sidecar is enough to route automatically to exact exclusion. The caller supplies no operational
identity to the dispatcher. -/
theorem start_rational_zero (numerator :
  Coherent.CoherentNamed) (input : Annotated)
    (threshold : Fraction.Rational) (positive : 0 < threshold) (zero : input.rationalValue = some 0) :
    (acquire numerator
      (Purelib.Approximation.Gaussian.Division.Acquisition.State.start input) threshold positive).2.status = .zero := by
  cases selected : input.provenance with
  | none => simp only [Annotated.rationalValue, selected] at zero; cases zero
  | some provenance =>
      cases provenance with
      | inr root => simp only [Annotated.rationalValue, selected] at zero; cases zero
      | inl rational =>
          have valueZero : rational.value = 0 := by
            apply Option.some.inj
            simpa only [Annotated.rationalValue, selected] using zero
          unfold acquire State.start
          dsimp only
          rw [selected]
          dsimp only
          dsimp only [Provenance.exact]
          unfold Approximation.Gaussian.Provenance.Rational.Basic.RationalSidecar.decide
          rw [dif_pos valueZero]
          rfl
end Purelib.Approximation.Gaussian.Division.Acquisition.Dispatch

end
