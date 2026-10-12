module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.Inspection
import Purelib.Approximation.Gaussian.Name.Coherent.Refinement.State
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction

public import Purelib.Approximation.Gaussian.Acquisition.Annotated.Basic
import Purelib.Approximation.Gaussian.Acquisition.Provenance
public import Purelib.Approximation.Gaussian.Division.Gap
public import Purelib.Approximation.Gaussian.Division.Search.State
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order
import Init.Prelude
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Approximation.Gaussian.Division.Prepared (Decision)

open Purelib

open Purelib.Approximation.Gaussian.Acquisition

open Purelib.Approximation.Gaussian.Division

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Name.Coherent

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

namespace Purelib.Approximation.Gaussian.Division.Acquisition.State

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Equivalence.Zero (ZeroIdentity)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

set_option genInjectivity false in
/-- Reusable denominator acquisition data indexed by the original coherent channel.

It retains the exact refinement state, optional finite provenance, cached exact decision and any state-indexed candidate
gap. -/
structure Input (channel : Coherent.CoherentNamed)
  where
  /-- The exact retained denominator refinement state. -/
  state : Approximation.Gaussian.Name.Coherent.Refinement.State channel
  /-- Optional supported finite provenance for the original channel. -/
  provenance : Option (Approximation.Gaussian.Acquisition.Provenance
    channel)
  /-- An optional exact denominator decision retained for reuse. -/
  cached : Option (Decision channel) := none
  /-- An optional candidate-gap certificate indexed by the retained state. -/ gap : Option (Gap.CandidateGap channel
    state) := none

constructive_injectivity Input

/-- Start acquisition at the annotated channel's original state and retain its provenance. -/
@[expose] def start (input :
    Approximation.Gaussian.Acquisition.Annotated)
  : Input input.channel :=
  { state := Approximation.Gaussian.Division.Search.State.initial input.channel
    provenance := input.provenance }

/-- The evidence route actually used by one acquisition step. -/
inductive Route where
  /-- Reuse an already retained exact denominator decision. -/ | cached /-- Derive an exact denominator decision from
    supported finite provenance. -/ | symbolic /-- Use the retained positive candidate-gap certificate. -/ | gap /--
    Make one finite numerical smallness-or-apartness inspection. -/ | numerical
  deriving DecidableEq

set_option genInjectivity false in
/-- The history records actual candidate persistence, not a falsely claimed canonical refinement step. Optional
provenance is kept unchanged. -/
structure Step {channel : Coherent.CoherentNamed}
  (input : Input channel) where
  /-- The acquisition input retained after the step. -/ next : Input
    channel
  /-- The evidence route used to obtain the retained result. -/ route :
    Route
  /-- The acquisition step preserves the exact original provenance sidecar. -/ provenance_eq : next.provenance =
    input.provenance
  /-- The acquisition step preserves the original canonical retry index. -/ index_eq : next.state.nextIndex =
    input.state.nextIndex
  /-- Every candidate at the retained next source remains a candidate at the original source. -/ persists : ∀ {value :
    Data.Gaussian.Basic.Canonical}, channel.name.process.Possible next.state.source value →
    channel.name.process.Possible input.state.source value

constructive_injectivity Step

/-- Record an acquisition route that leaves all input data unchanged. -/
@[expose] def Step.unchanged {channel :
  Coherent.CoherentNamed} (input : Input channel) (route :
  Route) : Step
  input :=
  ⟨input, route, rfl, rfl, fun possible => possible⟩

/-- Retain one finite inspection, preserve provenance and cached decisions, and transport the optional candidate gap. -/
@[expose] def Step.inspected {channel :
  Coherent.CoherentNamed} (input : Input channel) (route :
  Route)
    {target : Fraction.Rational} {positive : 0 < target}
    (inspection : Approximation.Gaussian.Name.Coherent.Refinement.Inspection channel input.state target positive) :
      Step input :=
  { next :=
      { state := inspection.retained
        provenance := input.provenance
        cached := input.cached
        gap := input.gap.map fun gap => gap.after inspection.possible_at_start }
    route := route
    provenance_eq := rfl
    index_eq := inspection.index_eq
    persists := inspection.possible_at_start }

/-- Cache the exact denominator decision in the retained next input without altering the step's state guarantees. -/
@[expose] def Step.cache {channel :
  Coherent.CoherentNamed} {input : Input channel}
    (step : Step input) (decision :
        Decision channel) :
      Step input :=
  { step with next := { step.next with cached := some decision } }

/-- Caching a decision retains exactly that decision for the next request. -/
@[simp] theorem Step.cache_reuses {channel :
  Coherent.CoherentNamed} {input : Input channel}
    (step : Step input) (decision :
        Decision channel) :
    (step.cache decision).next.cached = some decision := rfl
end Purelib.Approximation.Gaussian.Division.Acquisition.State

end
