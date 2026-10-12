module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Obstruction.Zero
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Gaussian.Division.Partial.Ready
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Approximation.Gaussian.Process.Based
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.Division.Acquisition.State
public import Purelib.Approximation.Gaussian.Division.Bounded.Certificate
import Purelib.Approximation.Gaussian.Division.Partial.ZeroObstruction
public import Purelib.Approximation.Gaussian.Division.Prepared.Quotient
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Zero
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Init.Core
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Acquisition

open Purelib.Approximation.Gaussian.Division.Bounded

open Purelib.Approximation.Gaussian.Division.Partial

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent.Refinement

open Purelib.Data.Rat

section
public section

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

namespace Purelib.Approximation.Gaussian.Division.Acquisition

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

namespace Report

set_option genInjectivity false in
/-- The certified result of denominator acquisition at its exact retained state.

The alternatives distinguish a cached quotient, global operational zero, branch-scoped zero and inconclusive threshold
smallness. -/
inductive Outcome (numerator channel :
  Coherent.CoherentNamed) (state : Name.Coherent.Refinement.State channel) (threshold : Fraction.Rational) : Type 1
  /-- Retain the cached ordinary quotient and its denominator preparation. -/ | ready (result : Prepared.Quotient
    numerator channel)
  /-- Retain a global operational zero identity for the original denominator channel. -/ | zero (identity :
    Zero.ZeroIdentity channel)
  /-- Retain exact-zero evidence for all candidates in this retained branch. -/ | branchZero (certificate :
    Zero.ZeroCandidates channel state)
  /-- Retain persistent threshold-smallness evidence at the exact inspected state. -/ | small (certificate :
    Certificate.SmallCertificate channel state threshold)

constructive_injectivity Outcome

/-- The finite tag identifying which certified acquisition outcome was returned. -/
inductive Status where
  /-- The outcome retains a certified quotient. -/ | ready /-- The outcome retains global operational zero. -/ | zero
    /-- The outcome retains branch-scoped candidate zero. -/ | branchZero /-- The outcome retains inconclusive threshold
    smallness. -/ | small
  deriving DecidableEq

end Report

namespace Report.Outcome

/-- Read the tag of the retained certified acquisition outcome. -/
@[expose] def status {numerator channel :
  Coherent.CoherentNamed} {state : Name.Coherent.Refinement.State channel} {threshold : Fraction.Rational} :
    Approximation.Gaussian.Division.Acquisition.Report.Outcome numerator channel state threshold →
      Approximation.Gaussian.Division.Acquisition.Report.Status
  | .ready _ => .ready
  | .zero _ => .zero
  | .branchZero _ => .branchZero
  | .small _ => .small

end Report.Outcome

/-- A denominator acquisition step and its outcome indexed by that step's exact retained state. -/
@[expose] def Report (numerator :
  Coherent.CoherentNamed) {channel : Coherent.CoherentNamed} (input : State.Input channel) (threshold :
  Fraction.Rational) :=
  Sigma fun step : State.Step input => Report.Outcome numerator channel
    step.next.state threshold

namespace Report

/-- Uniform public contract: successful output, global operational obstruction, branch-scoped obstruction, or persistent
threshold smallness. -/
theorem spec {numerator channel :
  Coherent.CoherentNamed} {input : State.Input channel} {threshold : Fraction.Rational}
    (report : Report numerator input threshold) :
    report.1.next.provenance = input.provenance ∧
    report.1.next.state.nextIndex = input.state.nextIndex ∧
    match report.2 with
    | .ready result => result.output = result.prepared.quotient numerator
    | .zero _ => ∀ (state : Name.Coherent.Refinement.State channel) (output : Coherent.CoherentNamed),
        Partial.Ready numerator channel state output → False
    | .branchZero _ => ∀ (state : Name.Coherent.Refinement.State channel),
        State.Reachable report.1.next.state state →
        ∀ (output : Coherent.CoherentNamed), Partial.Ready numerator channel state output → False
    | .small _ => ∀ (future : Gaussian.Process.Based.BasedState channel.name.process
          report.1.next.state.source) {value : Data.Gaussian.Basic.Canonical},
        channel.name.process.Possible future.source value →
          Data.Gaussian.Norm.Basic.normSq value < threshold := by
  refine ⟨report.1.provenance_eq, report.1.index_eq, ?_⟩
  cases report.2 with
  | ready result => exact result.output_eq
  | zero zero => exact fun _ _ ready => Obstruction.Zero.ZeroIdentity.no_ready zero ready
  | branchZero zero => exact fun _ path _ ready =>
      ZeroObstruction.ZeroCandidates.no_ready zero path ready
  | small small => exact fun future _value possible => small.candidates.at_future future possible

end Report

end Purelib.Approximation.Gaussian.Division.Acquisition

end
