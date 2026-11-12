module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
import Purelib.Riemann.Integration.RectangularPairedPointBanks
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularPairedSegments
import Purelib.Riemann.Paths.RectangularPairedTraceMagnitude
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedPairedTraceRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.EndpointJump
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.ClippedBilinearBudget
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian

open Purelib.Data.Rat

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation

open Purelib.Riemann.Normalization

open Purelib.Riemann.Paths

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Polygon

@[expose] public section

/-! Cross-face contact estimates for conjugate energy pairs. The existing
requests retain the common root and actual sheets; endpoint chords are kept. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks (TraceContactBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest (PairedTraceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation (PairedTracePreparation)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start : Gaussian} {owner : Owner
    (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {count : Nat} {points : Fin (count + 1) → Gaussian} {firstDifferential secondDifferential
    : Differential genus} {firstSheet secondSheet : Fin 2}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TracePreparation.PairedTracePreparation (AreaRequest)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Periods (ClippedBilinearBudget)

open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)

namespace PairedTraceRequest

variable {firstBank : TraceContactBank leftEntry
  rightEntry leftDomain rightDomain points firstDifferential firstSheet}
  {secondBank : TraceContactBank leftEntry
    rightEntry leftDomain rightDomain points secondDifferential secondSheet}
  {magnitude target : Coordinate} {floor : Nat}

/-- Gaussian conjugation preserves the difference of the original values. -/
private theorem conjugate_sub (first last : Gaussian) : Basic.conj (first -
  last) = Basic.conj first - Basic.conj last := by
  apply Basic.ext
  · rfl
  · simp only [Basic.conj, Basic.sub_im]; ring1

/-- Each actual centered conjugate trace discrepancy satisfies the retained paired contact error at a paid stage. -/
theorem conjugate_centered_accurate (request : TraceRequest.PairedTraceRequest firstBank secondBank magnitude target
  floor) {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : DomainPrimitives rightDomain secondDifferential stage)
    (leftFirst : PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : PointReadings secondRight.anchors secondRight.offsets points)
    (left : Sample (fun vertex => ⟨conj (leftFirst.values vertex), leftSecond.values vertex⟩))
    (right : Sample (fun vertex => ⟨conj (rightFirst.values vertex), rightSecond.values vertex⟩))
    (vertex : Fin (count + 1)) :
    PrimitivePoint.Bounded
      ((left.centered vertex).sub (right.centered vertex)) request.budget.error := by
  rw [left.centered_eq, right.centered_eq]
  have secondScalar := (request.second.accurate (request.second_le.trans later)
    secondLeft secondRight leftSecond rightSecond vertex).le
  rw [Norm.Basic.normSq_eq_canonical] at secondScalar
  refine ⟨?_, secondScalar⟩
  change Gaussian.normSq ((Basic.conj (leftFirst.values vertex) -
    Basic.conj (leftFirst.values 0)) -
    (Basic.conj (rightFirst.values vertex) - Basic.conj (rightFirst.values
      0))) ≤ _
  rw [← conjugate_sub, ←
    conjugate_sub, ←
    conjugate_sub, ←
    Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_conj,
    Norm.Basic.normSq_eq_canonical]
  have firstScalar := (request.first.accurate (request.first_le.trans later)
    firstLeft firstRight leftFirst rightFirst vertex).le
  simpa only [Norm.Basic.normSq_eq_canonical] using firstScalar

/-- The actual conjugate endpoint-increment correction is bounded using its original origin magnitude and retained
contact error. -/
theorem conjugate_endpointIncrementError_bound (request : TraceRequest.PairedTraceRequest firstBank secondBank magnitude
  target floor) {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : DomainPrimitives rightDomain secondDifferential stage)
    (leftFirst : PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : PointReadings secondRight.anchors secondRight.offsets points)
    (left : Sample (fun vertex => ⟨conj (leftFirst.values vertex), leftSecond.values vertex⟩))
    (right : Sample (fun vertex => ⟨conj (rightFirst.values vertex), rightSecond.values vertex⟩))
    {originMagnitude : Coordinate}
    (origin : PrimitivePoint.Bounded
      (⟨conj (rightFirst.values 0), rightSecond.values 0⟩ : Stokes.PrimitivePoint) originMagnitude) :
    Norm.Basic.normSq (left.endpointIncrementError right) ≤ 4 * originMagnitude *
      request.budget.error :=
  left.endpointIncrementError_bound right origin
    (conjugate_centered_accurate
      request later firstLeft firstRight secondLeft secondRight
      leftFirst rightFirst leftSecond rightSecond left right (Fin.last count))

/-- The actual endpoint-corrected conjugate paired trace-area discrepancy satisfies the retained target when the
original magnitude bound is supplied. -/
theorem conjugate_accurate (request : TraceRequest.PairedTraceRequest firstBank secondBank magnitude target floor)
  {stage : Nat}
    (later : request.index ≤ stage)
    (firstLeft : DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : DomainPrimitives rightDomain secondDifferential stage)
    (leftFirst : PointReadings firstLeft.anchors firstLeft.offsets points)
    (rightFirst : PointReadings firstRight.anchors firstRight.offsets points)
    (leftSecond : PointReadings secondLeft.anchors secondLeft.offsets points)
    (rightSecond : PointReadings secondRight.anchors secondRight.offsets points)
    (left : Sample (fun vertex => ⟨conj (leftFirst.values vertex), leftSecond.values vertex⟩))
    (right : Sample (fun vertex => ⟨conj (rightFirst.values vertex), rightSecond.values vertex⟩))
    (bounded : ∀ vertex, PrimitivePoint.Bounded
      (right.centered vertex) magnitude) :
    Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint -
      right.endpoint)) < target := by
  have errors (vertex : Fin (count + 1)) :
      PrimitivePoint.Bounded
        ((left.centered vertex).sub (right.centered vertex)) request.budget.error := by
    exact conjugate_centered_accurate
      request later firstLeft firstRight secondLeft secondRight
      leftFirst rightFirst leftSecond rightSecond left right vertex
  have estimate := left.comparison right request.budget.magnitude_nonnegative request.budget.error_positive.le
    request.budget.error_le_one bounded errors
  have paid := request.budget.error_paid
  rw [request.budget.weight_eq] at paid
  exact estimate.trans_lt ((show (count : Coordinate) ^ 2 * (32 * (magnitude + 1) *
    request.budget.error) =
    (count : Coordinate) ^ 2 * (32 * (magnitude + 1)) * request.budget.error by ring1).trans_lt
      paid)

end PairedTraceRequest
variable {piece : RectangularPairedSegments.PairedSegmentPiece leftDomain.geometry
  rightDomain.geometry}
  {trace : Riemann.Integration.RectangularPairedPointBanks.Trace piece count}

namespace PairedTracePreparation.AreaRequest

variable {preparation : PairedTracePreparation
  (leftEntry := leftEntry) (rightEntry := rightEntry) trace}
  {target : Coordinate} {floor : Nat}

/-- The prepared original conjugate trace request supplies its own retained magnitude bounds and pays the full
endpoint-corrected area target. -/
theorem conjugate_accurate (assembled : AreaRequest preparation firstDifferential
  secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.request.index ≤ stage)
    (firstLeft : DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : DomainPrimitives rightDomain secondDifferential stage)
    (left : Sample (fun vertex => ⟨conj ((trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Sample (fun vertex => ⟨conj ((trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint -
      right.endpoint)) < target := by
  apply PairedTraceRequest.conjugate_accurate
    assembled.request later firstLeft firstRight secondLeft secondRight
    (trace.leftReadings firstLeft.anchors firstLeft.offsets)
    (trace.rightReadings firstRight.anchors firstRight.offsets)
    (trace.leftReadings secondLeft.anchors secondLeft.offsets)
    (trace.rightReadings secondRight.anchors secondRight.offsets) left right
  intro vertex
  rw [right.centered_eq]
  have secondScalar := (RectangularPairedTraceMagnitude.right_increment_bound trace secondRight.anchors
    secondRight.offsets
    assembled.secondBounds rightDomain.patch.cell_refines vertex).trans (Fraction.Order.Basic.le_max_right
      (RectangularSeamBounds.boundarySlope assembled.firstBounds) _)
  rw [Norm.Basic.normSq_eq_canonical] at secondScalar
  refine ⟨?_, secondScalar⟩
  change Gaussian.normSq (Basic.conj ((trace.rightReadings
    firstRight.anchors firstRight.offsets).values vertex) -
    Basic.conj ((trace.rightReadings firstRight.anchors firstRight.offsets).values 0)) ≤ _
  rw [← PairedTraceRequest.conjugate_sub, ←
    Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_conj,
    Norm.Basic.normSq_eq_canonical]
  have firstScalar := (RectangularPairedTraceMagnitude.right_increment_bound trace firstRight.anchors firstRight.offsets
    assembled.firstBounds rightDomain.patch.cell_refines vertex).trans (Fraction.Order.Basic.le_max_left _
      (RectangularSeamBounds.boundarySlope assembled.secondBounds))
  simpa only [Norm.Basic.normSq_eq_canonical] using firstScalar

end PairedTracePreparation.AreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest
