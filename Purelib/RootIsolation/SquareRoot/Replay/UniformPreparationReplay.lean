module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Approximation.Rational.SquareRoot.Radius.Dyadic
import Purelib.Geometry.Rational.Box.Boundary
import Purelib.Geometry.Rational.Box.Square.Anchored
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Linearization
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.Newton.Restart.Separated.Basic
import Purelib.RootIsolation.Track.Basic
public import Purelib.RootIsolation.SquareRoot.Newton.Replay.Trace

import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.RootContinuation.CheckedSquareRootPreparation
import Purelib.Riemann.RootContinuation.SquareRootReconditioning
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticCoefficientClearance
public import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.FTA.Squarefree.Input
import Purelib.RootIsolation.Newton.Restart.Separated.Track
import Purelib.RootIsolation.SquareRoot.Newton.Search
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

@[expose] public section

/-! Rebuild the original uniform preparation from its checked occurrence
sample. The source square, restart track and strengthened owner retain their
canonical equations; no original sample search is evaluated by these builders. -/
namespace Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay

open Purelib.Riemann
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.UniformSquareRootPreparation

variable {polynomial : GaussianPolynomial} {ambient :
  UniformSquareRootPreparation.Box} {start finish :
  Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
    Coordinate)
  (inside : (0 : Coordinate) ≤ parameter ∧ parameter ≤ 1)
  (owner : Owner (polynomial.eval (segment.pointAt parameter)))
  (diameter : Coordinate) (positive : 0 < diameter)

/-- A retained Gaussian sample equal to the original uniform-preparation sample. -/
abbrev Saved := {point : Gaussian // point =
  sample segment owner diameter}

/-- The original eight-step checked Newton sampling trace at its prescribed grid and midpoint. -/
abbrev Samples := Newton.Replay.Trace
  (polynomial.eval (segment.pointAt parameter)) (SampleAcceptable
    segment owner diameter)
  8 (Approximation.Rational.SquareRoot.Radius.Dyadic.CheckedSquareRootNewton.gridFor
    (sampleResidualTarget segment owner diameter))
  (ownerMidpoint owner.track.initial.box)

/-- Recover the canonical preparation sample from the retained successful sampling trace. -/
def sampleFromTrace (trace : Samples segment parameter owner diameter)
    (accepted : {point : Gaussian //
      SampleAcceptable segment owner diameter point})
    (found : trace.result = some accepted) : Saved segment parameter owner
      diameter := by
  have candidates : sampleCandidates segment owner diameter = some
    accepted :=
    trace.result_eq.symm.trans found
  exact ⟨accepted.val, by unfold sample; rw [candidates]⟩

/-- Build the original anchored source square from the retained canonical sample and preparation radius. -/
def source (saved : Saved segment parameter owner diameter) :
  Geometry.Rational.Box :=
  Box.Square.Anchored.anchoredSquare saved.val (preparationRadius
    segment diameter)
    (preparationRadius_positive segment positive).le

section
open Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
/-- The replayed anchored square equals the original restart input's source box. -/
theorem source_eq (saved : Saved segment parameter owner diameter) :
    source segment parameter owner diameter positive saved =
      (restartInput segment parameter inside owner diameter
        positive).source := by
  rcases saved with ⟨point, same⟩
  cases same
  rfl

/-- Restore the separated restart input around the retained canonical sample.

The exact source-box equality transports the original residual, displacement and strict-target certificates while
preserving the original radius and Taylor bound. -/
def restart (saved : Saved segment parameter owner diameter) :
    Newton.Restart.Separated.Basic.SeparatedRestartInput
      (ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := rootAmbient segment) segment parameter inside) := by
  let original := restartInput segment parameter inside owner
    diameter positive
  let box := source segment parameter owner diameter positive saved
  have same : box = original.source := source_eq segment parameter inside
    owner diameter positive saved
  refine
    { source := box
      sourceRefines := same.symm ▸ original.sourceRefines
      residual := ?_
      threshold := ?_
      radius := preparationRadius segment diameter
      radiusPositive := preparationRadius_positive segment
        positive
      displacementBudget := ?_
      targetStrict := ?_
      taylorSmall := ?_ }
  · rw [same]
    exact original.residual
  · rw [same]
    exact original.threshold
  · rw [same]
    exact original.displacementBudget
  · rw [same]
    exact original.targetStrict
  · exact original.taylorSmall

end

/-- The replayed separated restart input is exactly the original uniform-preparation input. -/
theorem restart_eq (saved : Saved segment parameter owner diameter) :
    restart segment parameter inside owner diameter positive saved =
      restartInput segment parameter inside owner diameter
        positive := by
  rcases saved with ⟨point, same⟩
  cases same
  rfl

/-- Reconstruct the original centered winding-one track from the retained canonical sample.

The same separated restart, squarefree input, axis certificate and linearization majorant retain its original executable
construction. -/
def track (saved : Saved segment parameter owner diameter) :
    Track.Basic.WindingOneTrack
      (SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt parameter)))
      (restart segment parameter inside owner diameter positive
        saved).centeredBox := by
  let restored := restart segment parameter inside owner diameter positive
    saved
  let input := inputAt segment parameter inside
  let majorant := linearizationMajorant segment diameter
  have upper : ∀ z : Gaussian, Box.Boundary.OnBoxBoundary
    restored.centeredBox z →
      Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization
          (SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt
            parameter))) restored.source).eval z) ≤ majorant := by
    rw [show restored = restartInput segment parameter inside
      owner diameter positive from
      restart_eq segment parameter inside owner diameter positive saved]
    exact restart_newtonLinearization_boundary_le_majorant segment
      parameter inside owner diameter positive
  exact restored.centeredTrackWithMajorant input.squarefree
    (Clearance.QuadraticAxisElimination.quadraticAxisElimination (polynomial.eval (segment.pointAt
      parameter)))
    input.degreeAtLeastTwo majorant
      (linearizationMajorant_positive segment positive) upper

/-- Package the original nonzero parameter, restored centered ambient and reconstructed track as the quadratic owner. -/
def restoredOwner (saved : Saved segment parameter owner diameter) :
    Owner (polynomial.eval (segment.pointAt parameter)) where
  parameterNonzero := segment.pointAt_eval_ne_zero parameter inside
  ambient := (restart segment parameter inside owner diameter positive
    saved).centeredBox
  track := track segment parameter inside owner diameter positive saved

/-- The restored quadratic owner equals the original uniform-preparation owner. -/
theorem restoredOwner_eq (saved : Saved segment parameter owner diameter) :
    restoredOwner segment parameter inside owner diameter positive saved =
      prepared segment parameter inside owner diameter positive :=
        by
  rcases saved with ⟨point, same⟩
  cases same
  unfold restoredOwner
    prepared track
    UniformSquareRootPreparation.track
  rfl

/-- Apply the original coefficient-clearance strengthening to the restored quadratic owner. -/
def strengthened (saved : Saved segment parameter owner diameter) :=
  Clearance.QuadraticCoefficientClearance.strengthen
    (restoredOwner segment parameter inside owner diameter positive saved)

/-- Strengthening the restored owner equals strengthening the original uniform-preparation owner. -/
theorem strengthened_eq (saved : Saved segment parameter owner diameter) :
    strengthened segment parameter inside owner diameter positive saved =
      Clearance.QuadraticCoefficientClearance.strengthen
        (prepared segment parameter inside owner diameter
          positive) :=
  congrArg Clearance.QuadraticCoefficientClearance.strengthen
    (restoredOwner_eq segment parameter inside owner diameter positive saved)

/-- Restore the original cached prepared source after the checked-diameter proposal misses.

The retained canonical sample reconstructs the uniform fallback owner; its carrying certificate and exact owner equality
identify the same selected prepared source. -/
def cachedOfMiss (current : PreparedSheetContinuation.Endpoint)
    (sourceOwner : Owner (polynomial.eval (segment.pointAt
      current.parameter)))
    (request : PreparedSheetContinuation.StepRequest)
    (notReady : ¬ PreparedSheetContinuation.AlreadyPrepared segment current sourceOwner request)
    (candidate : CheckedSquareRootPreparation.Result segment current.parameter sourceOwner
      request.rootDiameter)
    (found : (CheckedSquareRootPreparation.attempt segment current.parameter sourceOwner
      request.rootDiameter).value = some candidate)
    (miss : ¬ ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      candidate.value.track.initial.clearance.bound)
    (saved : Saved segment current.parameter sourceOwner
      request.rootDiameter)
    (carries : ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      (strengthened segment current.parameter current.inside sourceOwner
        request.rootDiameter request.rootDiameterPositive saved).track.initial.clearance.bound) :
    PreparedSheetContinuation.CachedSource segment current sourceOwner request := by
  let value := strengthened segment current.parameter current.inside
    sourceOwner request.rootDiameter request.rootDiameterPositive saved
  have same := strengthened_eq segment current.parameter current.inside
    sourceOwner request.rootDiameter request.rootDiameterPositive saved
  have originalCarries := carries
  rw [same] at originalCarries
  exact ⟨value, same.trans (PreparedSheetContinuation.prepared_eq_uniform_of_not_ready_of_checked_miss
    segment current sourceOwner request notReady candidate found miss originalCarries).symm⟩

end Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
