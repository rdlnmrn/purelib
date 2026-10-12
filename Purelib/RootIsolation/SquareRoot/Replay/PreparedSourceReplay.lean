module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore

import Purelib.Elab.Deriving.Repr
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

public section

/-!
# Checked replay of recorded prepared-source choices

A recorded choice is untrusted finite data, not an equality certificate.
Replay checks the canonical branch conditions and uses the existing branch
equations to construct a `CachedSource`.  A failed check retains its actual
numerical inputs and proof; it does not run the remaining preparation search.
This component assumes the incoming owner has already been reconstructed.
It is not a codec for a complete prepared path or refinement state.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay

open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation

open Purelib.Riemann.Branches.PreparedSheetContinuation

/-- The rational coordinate field of retained source-readiness measurements. -/
abbrev Coordinate := Fraction.Rational
/-- The Gaussian coefficient type of the retained quadratic source. -/
abbrev Gaussian := Gaussian.Basic.Canonical
/-- The original dense Gaussian polynomial type. -/
abbrev Polynomial := Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The rational rectangle type used by the retained source owners. -/
abbrev Box := Purelib.Geometry.Rational.Box
/-- The exact quadratic owner used by source preparation and replay. -/
abbrev Owner := Riemann.Topology.SquareRootContinuationChain.Owner
/-- An original checked continuation endpoint. -/
abbrev Endpoint := Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint

/-- The selected stage of the original source-preparation sequence.

Inherited, strengthened and recentered stages retain their existing owners and are checked in that order. -/
inductive Hint where
  /-- Select the source owner inherited by the original continuation endpoint. -/ | inherited
  /-- Select the same-box strengthened owner from the original preparation sequence. -/ | strengthened
  /-- Select the original moving-recenter owner after same-box strengthening. -/ | recentered
deriving DecidableEq
derive_exposed_repr Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Hint

/-- The finite preparation order: inherited, strengthened, then recentered. -/
@[expose] def Hint.rank : SquareRoot.Replay.PreparedSourceReplay.Hint → Nat
  | .inherited => 0
  | .strengthened => 1
  | .recentered => 2

/-- Read the existing quadratic owner selected by the preparation hint. -/
@[expose] def Hint.owner {parameter : SquareRoot.Replay.PreparedSourceReplay.Gaussian} (hint :
  SquareRoot.Replay.PreparedSourceReplay.Hint) (source : SquareRoot.Replay.PreparedSourceReplay.Owner parameter) :
  SquareRoot.Replay.PreparedSourceReplay.Owner parameter :=
  match hint with
  | .inherited => source
  | .strengthened => SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner source
  | .recentered => Riemann.Branches.PreparedSheetContinuation.recentered source

variable {polynomial : Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Polynomial} {ambient :
  Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Box} {start finish :
  Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Gaussian}
variable (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (current :
  Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Endpoint)
variable (source : Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))) (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)

set_option genInjectivity false in
/-- Segment-wide readiness inputs shared by every owner at this diameter.
Their source equations preserve the original checker while avoiding repeated
finite radicand scans at each dyadic request and moving candidate. -/
structure Inputs (rootDiameter : SquareRoot.Replay.PreparedSourceReplay.Coordinate) where
  /-- The retained ambient box required by the original preparation. -/ requiredAmbient :
    SquareRoot.Replay.PreparedSourceReplay.Box
  /-- The retained ambient box equals the original required-ambient computation. -/ requiredAmbient_eq : requiredAmbient
    = Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment
  /-- The retained predicted displacement used for preparation. -/ predicted :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained displacement equals the original prediction. -/ predicted_eq : predicted =
    Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment rootDiameter

constructive_injectivity Inputs

/-- Cache the original preparation inputs together with their exact defining equalities. -/
@[expose] def Inputs.capture (rootDiameter : SquareRoot.Replay.PreparedSourceReplay.Coordinate) :
  SquareRoot.Replay.PreparedSourceReplay.Inputs segment rootDiameter where
  requiredAmbient := Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment
  requiredAmbient_eq := rfl
  predicted := Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment rootDiameter
  predicted_eq := rfl

set_option genInjectivity false in
/-- Cache the inputs of the finite readiness test, not merely its outcome. -/
structure Readiness (candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))) where
  /-- The selected original owner's retained box. -/ box : SquareRoot.Replay.PreparedSourceReplay.Box
  /-- The retained box is exactly the selected owner's box. -/ box_eq : box = candidate.track.initial.box
  /-- The required ambient box retained for this readiness comparison. -/ requiredAmbient :
    SquareRoot.Replay.PreparedSourceReplay.Box
  /-- The required ambient equals the original preparation input. -/ requiredAmbient_eq : requiredAmbient =
    Riemann.RootContinuation.UniformSquareRootPreparation.rootAmbient segment
  /-- The retained diameter of the selected original box. -/ diameter :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The diameter equals the original box-diameter computation. -/ diameter_eq : diameter = box.diagonalSq
  /-- The predicted movement retained for comparison with clearance. -/ predicted :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The movement reading equals the original prediction. -/ predicted_eq : predicted =
    Riemann.RootContinuation.UniformSquareRootPreparation.predictedClearance segment request.rootDiameter
  /-- The selected owner's retained clearance. -/ clearance : SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained clearance equals the original selected owner's clearance. -/ clearance_eq : clearance =
    candidate.track.initial.clearance.bound

constructive_injectivity Readiness

namespace Readiness

/-- Cache the selected owner's box, required ambient, diameter, predicted movement and clearance.

Every retained reading includes its equality to the original computation. -/
@[expose] def capture (candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter)))
    (inputs : SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter) :
    SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request candidate where
  box := candidate.track.initial.box
  box_eq := rfl
  requiredAmbient := inputs.requiredAmbient
  requiredAmbient_eq := inputs.requiredAmbient_eq
  diameter := candidate.track.initial.box.diagonalSq
  diameter_eq := rfl
  predicted := inputs.predicted
  predicted_eq := inputs.predicted_eq
  clearance := candidate.track.initial.clearance.bound
  clearance_eq := rfl

/-- Recover the shared inputs from an already captured candidate. -/
@[expose] def inputs {candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))}
    (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request candidate) :
      SquareRoot.Replay.PreparedSourceReplay.Inputs segment request.rootDiameter where
  requiredAmbient := data.requiredAmbient
  requiredAmbient_eq := data.requiredAmbient_eq
  predicted := data.predicted
  predicted_eq := data.predicted_eq

/-- The retained box is small enough, refines the required ambient and covers the predicted movement by its clearance.
-/
@[expose] def Ready {candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))}
    (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request candidate) : Prop :=
  data.diameter < request.rootDiameter ∧ data.predicted ≤ data.clearance ∧
    data.box.Refines data.requiredAmbient

/-- Decide readiness from its finite rational comparisons and box-refinement bounds. -/
instance {candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))}
    (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request candidate) : Decidable data.Ready
      := by
  unfold SquareRoot.Replay.PreparedSourceReplay.Readiness.Ready Box.Refines
  infer_instance

/-- The cached readiness conditions are exactly the original owner-preparation predicate. -/
theorem ready_iff {candidate : SquareRoot.Replay.PreparedSourceReplay.Owner (polynomial.eval (segment.pointAt
  current.parameter))}
    (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request candidate) :
    data.Ready ↔ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current candidate request := by
  simp only [SquareRoot.Replay.PreparedSourceReplay.Readiness.Ready,
    Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared, data.diameter_eq, data.box_eq,
    data.predicted_eq, data.clearance_eq, data.requiredAmbient_eq, -iff_self]
  exact Iff.rfl

end Readiness

set_option genInjectivity false in
/-- The one exact movement/clearance comparison that stopped replay. -/
structure Comparison (stage : SquareRoot.Replay.PreparedSourceReplay.Hint) where
  /-- The retained movement reading used by the actual carrying comparison. -/ movement :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained movement equals the original comparison's movement computation. -/ movement_eq : movement =
    Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
  /-- The retained source clearance used by the actual carrying comparison. -/ clearance :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained clearance equals the original comparison's clearance reading. -/ clearance_eq : clearance =
    (stage.owner source).track.initial.clearance.bound

constructive_injectivity Comparison

set_option genInjectivity false in
/-- The first failed obligation for this recorded choice.  This does not
claim that another choice, or the total preparation constructor, fails. -/
inductive Inconclusive (hint : SquareRoot.Replay.PreparedSourceReplay.Hint) where
  /-- Retain the attempted stage, its readiness readings and the failed readiness condition. -/ | notReady (stage :
    SquareRoot.Replay.PreparedSourceReplay.Hint)
      (data : SquareRoot.Replay.PreparedSourceReplay.Readiness segment current request (stage.owner source))
      (failed : ¬ data.Ready)
  /-- Retain an earlier preparation stage that already carries the target, preventing the requested stage from being the
    original selection. -/ | earlierCarries (stage : SquareRoot.Replay.PreparedSourceReplay.Hint) (earlier : stage.rank
    < hint.rank)
      (data : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request stage)
      (carries : data.movement < data.clearance)
  /-- Retain the selected stage's actual comparison showing that it does not carry the target. -/ | selectedMisses (data
    : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request hint)
      (misses : ¬ data.movement < data.clearance)

constructive_injectivity Inconclusive

set_option genInjectivity false in
/-- Retain the successful comparison too: constructing the integration edge
must not repeat the polynomial variation calculation merely to recover it. -/
structure Accepted where
  /-- The exact cached source selected by the original preparation. -/ cached :
    Riemann.Branches.PreparedSheetContinuation.CachedSource segment current source request
  /-- The retained movement reading used by the actual carrying comparison. -/ movement :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained movement equals the original comparison's movement computation. -/ movement_eq : movement =
    Riemann.Branches.ClearSheetContinuation.variationBound segment
    current.parameter request.endpoint.parameter
  /-- The retained source clearance used by the actual carrying comparison. -/ clearance :
    SquareRoot.Replay.PreparedSourceReplay.Coordinate
  /-- The retained clearance equals the original comparison's clearance reading. -/ clearance_eq : clearance =
    cached.preparedOwner.track.initial.clearance.bound
  /-- The retained movement and clearance prove that this actual cached source carries the target. -/ carries : movement
    < clearance

constructive_injectivity Accepted

/-- Check a recorded same-box/first-recenter choice without evaluating the
remaining canonical retry budget.  Unsupported or stale choices retain the
failed readiness/comparison data; they are never silently replaced by a search. -/
@[expose] def replay (hint : SquareRoot.Replay.PreparedSourceReplay.Hint) :
    Except (SquareRoot.Replay.PreparedSourceReplay.Inconclusive segment current source request hint)
      (SquareRoot.Replay.PreparedSourceReplay.Accepted segment current source request) := by
  let inputs := SquareRoot.Replay.PreparedSourceReplay.Inputs.capture segment request.rootDiameter
  let initial := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request source inputs
  by_cases ready : initial.Ready
  · have sourceReady := initial.ready_iff.mp ready
    let movement := Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter
    let original : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request .inherited :=
      ⟨movement, rfl, initial.clearance, initial.clearance_eq⟩
    cases hint with
    | inherited =>
        by_cases carries : original.movement < original.clearance
        · have carriesSource : movement < source.track.initial.clearance.bound := by
            simpa only [original, initial.clearance_eq] using carries
          exact .ok
            { cached := ⟨source, (Riemann.Branches.PreparedSheetContinuation.prepared_eq_self_of_ready segment current
              source request sourceReady carriesSource).symm⟩,
              movement := original.movement, movement_eq := original.movement_eq,
              clearance := original.clearance, clearance_eq := original.clearance_eq,
              carries := carries }
        · exact .error (.selectedMisses original carries)
    | strengthened =>
        by_cases carries : original.movement < original.clearance
        · exact .error (.earlierCarries .inherited (by decide) original carries)
        · have missesSource : ¬ movement < source.track.initial.clearance.bound := by
            simpa only [original, initial.clearance_eq] using carries
          let candidate := SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner source
          let check : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request .strengthened :=
            ⟨movement, rfl, candidate.track.initial.clearance.bound, rfl⟩
          by_cases candidateCarries : check.movement < check.clearance
          · exact .ok
              { cached := ⟨candidate,
                (Riemann.Branches.PreparedSheetContinuation.prepared_eq_strengthenQuadraticOwner_of_ready segment
                current source request
                  sourceReady missesSource candidateCarries).symm⟩,
                movement := check.movement, movement_eq := check.movement_eq,
                clearance := check.clearance, clearance_eq := check.clearance_eq,
                carries := candidateCarries }
          · exact .error (.selectedMisses check candidateCarries)
    | recentered =>
        by_cases carries : original.movement < original.clearance
        · exact .error (.earlierCarries .inherited (by decide) original carries)
        · have missesSource : ¬ movement < source.track.initial.clearance.bound := by
            simpa only [original, initial.clearance_eq] using carries
          let strengthened := SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner source
          let check : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request .strengthened :=
            ⟨movement, rfl, strengthened.track.initial.clearance.bound, rfl⟩
          by_cases strengthenedCarries : check.movement < check.clearance
          · exact .error (.earlierCarries .strengthened (by decide) check strengthenedCarries)
          · let candidate := Riemann.Branches.PreparedSheetContinuation.recentered source
            let data := SquareRoot.Replay.PreparedSourceReplay.Readiness.capture segment current request candidate
              inputs
            by_cases candidateReady : data.Ready
            · let final : SquareRoot.Replay.PreparedSourceReplay.Comparison segment current source request .recentered
                :=
                ⟨movement, rfl, data.clearance, data.clearance_eq⟩
              by_cases candidateCarries : final.movement < final.clearance
              · have carriesCandidate : movement < candidate.track.initial.clearance.bound := by
                  simpa only [final, data.clearance_eq] using candidateCarries
                exact .ok
                  { cached := ⟨candidate, (Riemann.Branches.PreparedSheetContinuation.prepared_eq_recentered_of_ready
                    segment current source request
                      sourceReady missesSource strengthenedCarries (data.ready_iff.mp candidateReady)
                        carriesCandidate).symm⟩,
                    movement := final.movement, movement_eq := final.movement_eq,
                    clearance := final.clearance, clearance_eq := final.clearance_eq,
                    carries := candidateCarries }
              · exact .error (.selectedMisses final candidateCarries)
            · exact .error (.notReady .recentered data candidateReady)
  · exact .error (.notReady .inherited initial ready)

end Purelib.RootIsolation.SquareRoot.Replay.PreparedSourceReplay

end
