module
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Newton.Search.Attempt
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.Track.Accelerated
import Purelib.RootIsolation.Track.Basic

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
public import Purelib.Riemann.RootContinuation.SquareRootOwnerFamily
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw

open Purelib

open Purelib.Data

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-!
Exact sample replay follows the original track's checked first attempt, not
an equality to a newly chosen total refiner.  In particular, accelerating an
isolated track keeps its original fallback.  The finite law below suffices
for every accepted sample step and is preserved by the original preparation
and transport constructors.  It introduces no convergence assumption.
-/

namespace Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay

open QuadraticSampleReplay (Coordinate Gaussian Box State attempt)

open Purelib.Riemann.Integration
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches

/-- The original winding-one track of the quadratic polynomial in the retained ambient box. -/
abbrev Track (parameter : Gaussian) (ambient : Box) :=
  Track.Basic.WindingOneTrack
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter Riemann.RootContinuation.SquareRootDegree.degreeTwo)
      ambient

/-- Only the successful first-attempt equation is required; the original
total fallback and its source history remain completely unchanged. -/
def CheckedFirst {parameter : Gaussian} {ambient : Box} (track : SquareRoot.Replay.QuadraticTrackReplay.Track parameter
  ambient) : Prop :=
  ∀ (current : State parameter ambient) (epsilon : Coordinate) (positive : 0 < epsilon)
    (accepted : Refinement current.raw epsilon),
    attempt current epsilon = some accepted → track.refine current epsilon positive = accepted.state

/-- The retained owner's original track agrees with every successful bounded first attempt. -/
abbrev Ready {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter) :=
  SquareRoot.Replay.QuadraticTrackReplay.CheckedFirst owner.track

/-- An accelerated quadratic track agrees with every successful original first attempt. -/
theorem accelerated {parameter : Gaussian} {ambient : Box} (track : SquareRoot.Replay.QuadraticTrackReplay.Track
  parameter ambient) :
    SquareRoot.Replay.QuadraticTrackReplay.CheckedFirst
      (SquareRoot.Clearance.QuadraticLineClearance.Owner.accelerateTrack parameter track) := by
  intro current epsilon positive accepted found
  change (Track.Accelerated.refinement _ track current epsilon positive _).state = _
  unfold Track.Accelerated.refinement
  rw [show Newton.Search.Attempt.attempt _ current.raw epsilon _ = some accepted from found]

/-- Both original quadratic track recipes satisfy the checked first-attempt equation. -/
theorem recipe (value : SquareRoot.Replay.QuadraticSampleReplay.Recipe) {parameter : Gaussian} {ambient : Box}
    (nonzero : parameter ≠ 0) (initial : State parameter ambient) :
    SquareRoot.Replay.QuadraticTrackReplay.CheckedFirst (value.track nonzero initial) :=
  SquareRoot.Replay.QuadraticSampleReplay.refine_eq_of_attempt value nonzero initial

/-- A retained matching recipe proves readiness of the same original quadratic owner. -/
theorem ofRecipe {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
    (value : SquareRoot.Replay.QuadraticSampleReplay.Recipe) (same : value.Matches owner) :
      SquareRoot.Replay.QuadraticTrackReplay.Ready owner := by
  rw [SquareRoot.Replay.QuadraticTrackReplay.Ready, ← same]
  exact SquareRoot.Replay.QuadraticTrackReplay.recipe value _ _

/-- The deferred quadratic owner satisfies the checked first-attempt equation. -/
theorem deferred {parameter : Gaussian} {ambient : Box} (nonzero : parameter ≠ 0)
    (initial : State parameter ambient) : SquareRoot.Replay.QuadraticTrackReplay.Ready
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.ownerOfState nonzero initial) :=
  SquareRoot.Replay.QuadraticTrackReplay.recipe .deferred nonzero initial

/-- The quadratic owner constructed from a retained state satisfies the checked first-attempt equation. -/
theorem ofState {parameter : Gaussian} {ambient : Box} (nonzero : parameter ≠ 0)
    (initial : State parameter ambient) : SquareRoot.Replay.QuadraticTrackReplay.Ready
      (Riemann.Topology.SquareRootContinuationChain.Owner.ofState nonzero initial) :=
  SquareRoot.Replay.QuadraticTrackReplay.accelerated _

/-- The independently constructed owner at the supplied sheet satisfies the checked first-attempt equation. -/
theorem independent {parameter : Gaussian} (nonzero : parameter ≠ 0) (sheet : Fin 2) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Topology.SquareRootContinuationChain.Owner.independent nonzero
      sheet) := SquareRoot.Replay.QuadraticTrackReplay.accelerated _

/-- Each owner in the retained independent square-root family satisfies the checked first-attempt equation. -/
theorem family {parameter : Gaussian} (source : Riemann.RootContinuation.SquareRootOwnerFamily.IndependentFamily
  parameter) (sheet : Fin 2) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (source.owner sheet) :=
      SquareRoot.Replay.QuadraticTrackReplay.accelerated _

/-- Strengthening the quadratic coefficient clearance produces a ready original owner. -/
theorem coefficient {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen owner)
      := SquareRoot.Replay.QuadraticTrackReplay.deferred _ _

/-- Exact quadratic owner strengthening preserves readiness through its unchanged or deferred branches. -/
theorem strengthened {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
  (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner owner) := by
  rcases SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner_source_or_deferred owner with same |
    ⟨_, _, same⟩
  · rw [same]; exact ready
  · rw [same]; exact SquareRoot.Replay.QuadraticTrackReplay.deferred _ _

/-- Recentering preserves readiness of the retained owner or of its certified deferred reset. -/
theorem recentered {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter) (ready
  : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.recentered owner) := by
  unfold Riemann.Branches.PreparedSheetContinuation.recentered
  split
  · exact ready
  · rename_i reset _
    rw [reset.deferred]
    exact SquareRoot.Replay.QuadraticTrackReplay.deferred _ _

/-- Retaining a requested reserve preserves the checked first-attempt equation.

The proof follows the original unchanged, coefficient-strengthened and recentered branches. -/
theorem retained {parameter : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter) (ready :
  SquareRoot.Replay.QuadraticTrackReplay.Ready owner)
    (reserve : Coordinate) : SquareRoot.Replay.QuadraticTrackReplay.Ready
      (Riemann.Branches.PreparedSheetContinuation.retainedAtReserve owner reserve) := by
  unfold Riemann.Branches.PreparedSheetContinuation.retainedAtReserve
  split
  · exact ready
  · dsimp only
    split
    · exact SquareRoot.Replay.QuadraticTrackReplay.coefficient _
    · exact SquareRoot.Replay.QuadraticTrackReplay.recentered _ ready

/-- The owner advanced under the supplied parameter-distance bound satisfies the checked first-attempt equation. -/
theorem advanced {source target : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner source) (nonzero
  : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (owner.advance nonzero small) :=
      SquareRoot.Replay.QuadraticTrackReplay.accelerated _

/-- Resultant-based reserved transport produces a ready quadratic owner in every original branch. -/
private theorem resultant {source target : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner source)
  (nonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (reserve : Coordinate) : SquareRoot.Replay.QuadraticTrackReplay.Ready
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.resultantReservedTransport owner nonzero small reserve) := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.resultantReservedTransport
  dsimp only
  split_ifs <;> first
    | exact SquareRoot.Replay.QuadraticTrackReplay.deferred _ _
    | exact SquareRoot.Replay.QuadraticTrackReplay.advanced _ _ _
    | (split
       · rename_i moved _
         rw [moved.deferred]
         exact SquareRoot.Replay.QuadraticTrackReplay.deferred _ _
       · exact SquareRoot.Replay.QuadraticTrackReplay.advanced _ _ _)

/-- Reserved quadratic transport preserves readiness.

Stationary transport retains the original ready owner; nonstationary transport uses the existing resultant construction.
-/
theorem transported {source target : Gaussian} (owner : Riemann.Topology.SquareRootContinuationChain.Owner source)
  (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner)
    (nonzero : target ≠ 0)
    (small : Data.Gaussian.Norm.Basic.normSq (source - target) < owner.track.initial.clearance.bound)
    (reserve : Coordinate) : SquareRoot.Replay.QuadraticTrackReplay.Ready
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport owner nonzero small reserve) := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.reservedTransport
  split
  · rename_i same
    subst target
    exact ready
  · dsimp only
    split_ifs <;> first
      | exact SquareRoot.Replay.QuadraticTrackReplay.deferred _ _
      | exact SquareRoot.Replay.QuadraticTrackReplay.resultant _ _ _ _

/-- The owner of a checked quadratic preparation satisfies the checked first-attempt equation. -/
theorem checkedPreparation
    {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {start
      finish : Gaussian}
    (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter : Coordinate)
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt parameter))) (diameter
      : Coordinate)
    (accepted : Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment parameter owner diameter)
    (found : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment parameter owner
      diameter).value = some
      accepted) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready accepted.value :=
  SquareRoot.Replay.QuadraticTrackReplay.ofRecipe accepted.value .deferred
    (SquareRoot.Replay.QuadraticSampleReplay.matches_checkedPreparation segment parameter owner diameter accepted found)

section Preparation

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
  {start finish : Gaussian} (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish)
  (current : Riemann.Branches.PreparedSheetContinuation.Endpoint)
  (owner : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt current.parameter)))
  (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)

/-- The original uniform preparation yields a ready quadratic owner. -/
private theorem uniform : SquareRoot.Replay.QuadraticTrackReplay.Ready
  (Riemann.Branches.PreparedSheetContinuation.uniformPrepared segment current owner request) :=
  SquareRoot.Replay.QuadraticTrackReplay.coefficient _

/-- The original baseline preparation yields a ready quadratic owner. -/
private theorem baseline (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.baselinePrepared segment
      current owner request) := by
  unfold Riemann.Branches.PreparedSheetContinuation.baselinePrepared
  split
  · split
    · exact ready
    · exact SquareRoot.Replay.QuadraticTrackReplay.strengthened _ ready
  · split
    · rename_i accepted found
      exact SquareRoot.Replay.QuadraticTrackReplay.checkedPreparation _ _ _ _ accepted found
    · exact SquareRoot.Replay.QuadraticTrackReplay.uniform segment current owner request

/-- One original preparation retry preserves readiness of the retained owner. -/
private theorem retried
    (moved : Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval (segment.pointAt current.parameter)))
      (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready moved)
    (retry : Riemann.Branches.PreparedSheetContinuation.CoefficientRetry segment current owner request moved) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.CoefficientRetry.value
      retry) := by
  cases Riemann.Branches.PreparedSheetContinuation.CoefficientRetry.origin retry with
  | coefficient equal => rw [equal]; exact SquareRoot.Replay.QuadraticTrackReplay.coefficient _
  | movedCoefficient equal => rw [equal]; exact SquareRoot.Replay.QuadraticTrackReplay.coefficient _
  | movedBaseline equal =>
      rw [equal]
      exact SquareRoot.Replay.QuadraticTrackReplay.baseline segment current moved request ready
  | secondReset equal => rw [equal]; exact SquareRoot.Replay.QuadraticTrackReplay.recentered _ ready

/-- The original finite preparation retry sequence preserves readiness of its final owner. -/
private theorem withRetries (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) (count : Nat) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.preparedWithRetries segment
      current owner request count) := by
  induction count generalizing owner with
  | zero =>
      unfold Riemann.Branches.PreparedSheetContinuation.preparedWithRetries
      dsimp only
      split
      · exact SquareRoot.Replay.QuadraticTrackReplay.baseline segment current owner request ready
      · exact SquareRoot.Replay.QuadraticTrackReplay.uniform segment current owner request
  | succ count ih =>
      unfold Riemann.Branches.PreparedSheetContinuation.preparedWithRetries
      dsimp only
      split
      · exact SquareRoot.Replay.QuadraticTrackReplay.baseline segment current owner request ready
      · split
        · split
          · exact SquareRoot.Replay.QuadraticTrackReplay.uniform segment current owner request
          · exact ih _ (SquareRoot.Replay.QuadraticTrackReplay.recentered owner ready)
        · split
          · rename_i retry _
            exact SquareRoot.Replay.QuadraticTrackReplay.retried segment current owner request _
              (SquareRoot.Replay.QuadraticTrackReplay.recentered owner ready) retry
          · exact ih _ (SquareRoot.Replay.QuadraticTrackReplay.recentered owner ready)

/-- Every branch of the existing total preparation preserves the checked
first attempt.  No accepted-depth or constructor-recipe premise is needed. -/
theorem prepared (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.prepared segment current
      owner request) := by
  unfold Riemann.Branches.PreparedSheetContinuation.prepared
  exact SquareRoot.Replay.QuadraticTrackReplay.withRetries segment current owner request ready _

/-- The owner retained by cached preparation satisfies the checked first-attempt equation. -/
theorem cached (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner)
    (cache : Riemann.Branches.PreparedSheetContinuation.CachedSource segment current owner request) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready cache.preparedOwner := by
  rw [cache.preparedOwner_eq]
  exact SquareRoot.Replay.QuadraticTrackReplay.prepared segment current owner request ready

/-- Prepared owner advancement preserves readiness at the new parameter. -/
theorem advance (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) (within : segment.WithinAmbient)
    (small : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
      <
      (Riemann.Branches.PreparedSheetContinuation.prepared segment current owner request).track.initial.clearance.bound)
        :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.advance segment within
      current owner request small) := by
  apply SquareRoot.Replay.QuadraticTrackReplay.retained
  exact SquareRoot.Replay.QuadraticTrackReplay.transported _ (SquareRoot.Replay.QuadraticTrackReplay.prepared segment
    current owner request ready) _ _ _

/-- Cached prepared owner advancement preserves readiness at the new parameter. -/
theorem advanceCached (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready owner) (within : segment.WithinAmbient)
    (cache : Riemann.Branches.PreparedSheetContinuation.CachedSource segment current owner request)
    (small : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter request.endpoint.parameter
      <
      cache.preparedOwner.track.initial.clearance.bound) :
    SquareRoot.Replay.QuadraticTrackReplay.Ready (Riemann.Branches.PreparedSheetContinuation.advanceCached segment
      within current owner request cache small) := by
  apply SquareRoot.Replay.QuadraticTrackReplay.retained
  exact SquareRoot.Replay.QuadraticTrackReplay.transported _ (SquareRoot.Replay.QuadraticTrackReplay.cached segment
    current owner request ready cache) _ _ _

end Preparation

/-- The owner returned by the original base query satisfies the checked first-attempt equation. -/
theorem baseQuery {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Curves.Hyperelliptic.Differentials.Basic.Differential genus}
    (edge : Riemann.Integration.PreparedConstantModels.PreparedEdge curve differential)
    (ready : SquareRoot.Replay.QuadraticTrackReplay.Ready edge.cached.preparedOwner) :
      SquareRoot.Replay.QuadraticTrackReplay.Ready (edge.directQueryOwner 0 edge.baseInside) :=
  SquareRoot.Replay.QuadraticTrackReplay.transported _ ready _ _ _

end Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
