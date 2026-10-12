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

variable {polynomial : Riemann.RootContinuation.UniformSquareRootPreparation.GaussianPolynomial} {ambient :
  Riemann.RootContinuation.UniformSquareRootPreparation.Box} {start finish :
  Riemann.RootContinuation.UniformSquareRootPreparation.Gaussian}
  (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish) (parameter :
    Riemann.RootContinuation.UniformSquareRootPreparation.Coordinate)
  (inside : (0 : Riemann.RootContinuation.UniformSquareRootPreparation.Coordinate) ≤ parameter ∧ parameter ≤ 1)
  (owner : Riemann.RootContinuation.UniformSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter)))
  (diameter : Riemann.RootContinuation.UniformSquareRootPreparation.Coordinate) (positive : 0 < diameter)

/-- A retained Gaussian sample equal to the original uniform-preparation sample. -/
abbrev Saved := {point : Riemann.RootContinuation.UniformSquareRootPreparation.Gaussian // point =
  Riemann.RootContinuation.UniformSquareRootPreparation.sample segment owner diameter}

/-- The original eight-step checked Newton sampling trace at its prescribed grid and midpoint. -/
abbrev Samples := Newton.Replay.Trace
  (polynomial.eval (segment.pointAt parameter)) (Riemann.RootContinuation.UniformSquareRootPreparation.SampleAcceptable
    segment owner diameter)
  8 (Approximation.Rational.SquareRoot.Radius.Dyadic.CheckedSquareRootNewton.gridFor
    (Riemann.RootContinuation.UniformSquareRootPreparation.sampleResidualTarget segment owner diameter))
  (Riemann.RootContinuation.UniformSquareRootPreparation.ownerMidpoint owner.track.initial.box)

/-- Recover the canonical preparation sample from the retained successful sampling trace. -/
def sampleFromTrace (trace : SquareRoot.Replay.UniformPreparationReplay.Samples segment parameter owner diameter)
    (accepted : {point : Riemann.RootContinuation.UniformSquareRootPreparation.Gaussian //
      Riemann.RootContinuation.UniformSquareRootPreparation.SampleAcceptable segment owner diameter point})
    (found : trace.result = some accepted) : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner
      diameter := by
  have candidates : Riemann.RootContinuation.UniformSquareRootPreparation.sampleCandidates segment owner diameter = some
    accepted :=
    trace.result_eq.symm.trans found
  exact ⟨accepted.val, by unfold Riemann.RootContinuation.UniformSquareRootPreparation.sample; rw [candidates]⟩

/-- Build the original anchored source square from the retained canonical sample and preparation radius. -/
def source (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
  Purelib.Geometry.Rational.Box :=
  Box.Square.Anchored.anchoredSquare saved.val (Riemann.RootContinuation.UniformSquareRootPreparation.preparationRadius
    segment diameter)
    (Riemann.RootContinuation.UniformSquareRootPreparation.preparationRadius_positive segment positive).le

section
open Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
/-- The replayed anchored square equals the original restart input's source box. -/
theorem source_eq (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    source segment parameter owner diameter positive saved =
      (Riemann.RootContinuation.UniformSquareRootPreparation.restartInput segment parameter inside owner diameter
        positive).source := by
  rcases saved with ⟨point, same⟩
  cases same
  rfl

/-- Restore the separated restart input around the retained canonical sample.

The exact source-box equality transports the original residual, displacement and strict-target certificates while
preserving the original radius and Taylor bound. -/
def restart (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    Newton.Restart.Separated.Basic.SeparatedRestartInput
      (Riemann.Branches.ClearSheetContinuation.squareRootDerivativeSeparation
        (rootAmbient := rootAmbient segment) segment parameter inside) := by
  let original := Riemann.RootContinuation.UniformSquareRootPreparation.restartInput segment parameter inside owner
    diameter positive
  let box := source segment parameter owner diameter positive saved
  have same : box = original.source := SquareRoot.Replay.UniformPreparationReplay.source_eq segment parameter inside
    owner diameter positive saved
  refine
    { source := box
      sourceRefines := same.symm ▸ original.sourceRefines
      residual := ?_
      threshold := ?_
      radius := Riemann.RootContinuation.UniformSquareRootPreparation.preparationRadius segment diameter
      radiusPositive := Riemann.RootContinuation.UniformSquareRootPreparation.preparationRadius_positive segment
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
theorem restart_eq (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    SquareRoot.Replay.UniformPreparationReplay.restart segment parameter inside owner diameter positive saved =
      Riemann.RootContinuation.UniformSquareRootPreparation.restartInput segment parameter inside owner diameter
        positive := by
  rcases saved with ⟨point, same⟩
  cases same
  rfl

/-- Reconstruct the original centered winding-one track from the retained canonical sample.

The same separated restart, squarefree input, axis certificate and linearization majorant retain its original executable
construction. -/
def track (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    Track.Basic.WindingOneTrack
      (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt parameter)))
      (SquareRoot.Replay.UniformPreparationReplay.restart segment parameter inside owner diameter positive
        saved).centeredBox := by
  let restored := SquareRoot.Replay.UniformPreparationReplay.restart segment parameter inside owner diameter positive
    saved
  let input := UniformSquareRootPreparation.inputAt segment parameter inside
  let majorant := Riemann.RootContinuation.UniformSquareRootPreparation.linearizationMajorant segment diameter
  have upper : ∀ z : Riemann.RootContinuation.UniformSquareRootPreparation.Gaussian, Box.Boundary.OnBoxBoundary
    restored.centeredBox z →
      Data.Gaussian.Norm.Basic.normSq
        ((Dense.Gaussian.Newton.Box.Linearization.newtonLinearization
          (Riemann.RootContinuation.SquareRootReconditioning.rootPolynomial (polynomial.eval (segment.pointAt
            parameter))) restored.source).eval z) ≤ majorant := by
    rw [show restored = Riemann.RootContinuation.UniformSquareRootPreparation.restartInput segment parameter inside
      owner diameter positive from
      SquareRoot.Replay.UniformPreparationReplay.restart_eq segment parameter inside owner diameter positive saved]
    exact Riemann.RootContinuation.UniformSquareRootPreparation.restart_newtonLinearization_boundary_le_majorant segment
      parameter inside owner diameter positive
  exact restored.centeredTrackWithMajorant input.squarefree
    (SquareRoot.Clearance.QuadraticAxisElimination.quadraticAxisElimination (polynomial.eval (segment.pointAt
      parameter)))
    input.degreeAtLeastTwo majorant
      (Riemann.RootContinuation.UniformSquareRootPreparation.linearizationMajorant_positive segment positive) upper

/-- Package the original nonzero parameter, restored centered ambient and reconstructed track as the quadratic owner. -/
def restoredOwner (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    Riemann.RootContinuation.UniformSquareRootPreparation.Owner (polynomial.eval (segment.pointAt parameter)) where
  parameterNonzero := segment.pointAt_eval_ne_zero parameter inside
  ambient := (SquareRoot.Replay.UniformPreparationReplay.restart segment parameter inside owner diameter positive
    saved).centeredBox
  track := SquareRoot.Replay.UniformPreparationReplay.track segment parameter inside owner diameter positive saved

/-- The restored quadratic owner equals the original uniform-preparation owner. -/
theorem restoredOwner_eq (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    SquareRoot.Replay.UniformPreparationReplay.restoredOwner segment parameter inside owner diameter positive saved =
      Riemann.RootContinuation.UniformSquareRootPreparation.prepared segment parameter inside owner diameter positive :=
        by
  rcases saved with ⟨point, same⟩
  cases same
  unfold SquareRoot.Replay.UniformPreparationReplay.restoredOwner
    Riemann.RootContinuation.UniformSquareRootPreparation.prepared SquareRoot.Replay.UniformPreparationReplay.track
    Riemann.RootContinuation.UniformSquareRootPreparation.track
  rfl

/-- Apply the original coefficient-clearance strengthening to the restored quadratic owner. -/
def strengthened (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :=
  SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen
    (SquareRoot.Replay.UniformPreparationReplay.restoredOwner segment parameter inside owner diameter positive saved)

/-- Strengthening the restored owner equals strengthening the original uniform-preparation owner. -/
theorem strengthened_eq (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment parameter owner diameter) :
    SquareRoot.Replay.UniformPreparationReplay.strengthened segment parameter inside owner diameter positive saved =
      SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen
        (Riemann.RootContinuation.UniformSquareRootPreparation.prepared segment parameter inside owner diameter
          positive) :=
  congrArg SquareRoot.Clearance.QuadraticCoefficientClearance.strengthen
    (SquareRoot.Replay.UniformPreparationReplay.restoredOwner_eq segment parameter inside owner diameter positive saved)

/-- Restore the original cached prepared source after the checked-diameter proposal misses.

The retained canonical sample reconstructs the uniform fallback owner; its carrying certificate and exact owner equality
identify the same selected prepared source. -/
def cachedOfMiss (current : Riemann.Branches.PreparedSheetContinuation.Endpoint)
    (sourceOwner : Riemann.RootContinuation.UniformSquareRootPreparation.Owner (polynomial.eval (segment.pointAt
      current.parameter)))
    (request : Riemann.Branches.PreparedSheetContinuation.StepRequest)
    (notReady : ¬ Riemann.Branches.PreparedSheetContinuation.AlreadyPrepared segment current sourceOwner request)
    (candidate : Riemann.RootContinuation.CheckedSquareRootPreparation.Result segment current.parameter sourceOwner
      request.rootDiameter)
    (found : (Riemann.RootContinuation.CheckedSquareRootPreparation.attempt segment current.parameter sourceOwner
      request.rootDiameter).value = some candidate)
    (miss : ¬ Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      candidate.value.track.initial.clearance.bound)
    (saved : SquareRoot.Replay.UniformPreparationReplay.Saved segment current.parameter sourceOwner
      request.rootDiameter)
    (carries : Riemann.Branches.ClearSheetContinuation.variationBound segment current.parameter
      request.endpoint.parameter <
      (SquareRoot.Replay.UniformPreparationReplay.strengthened segment current.parameter current.inside sourceOwner
        request.rootDiameter request.rootDiameterPositive saved).track.initial.clearance.bound) :
    Riemann.Branches.PreparedSheetContinuation.CachedSource segment current sourceOwner request := by
  let value := SquareRoot.Replay.UniformPreparationReplay.strengthened segment current.parameter current.inside
    sourceOwner request.rootDiameter request.rootDiameterPositive saved
  have same := SquareRoot.Replay.UniformPreparationReplay.strengthened_eq segment current.parameter current.inside
    sourceOwner request.rootDiameter request.rootDiameterPositive saved
  have originalCarries := carries
  rw [same] at originalCarries
  exact ⟨value, same.trans (Riemann.Branches.PreparedSheetContinuation.prepared_eq_uniform_of_not_ready_of_checked_miss
    segment current sourceOwner request notReady candidate found miss originalCarries).symm⟩

end Purelib.RootIsolation.SquareRoot.Replay.UniformPreparationReplay
