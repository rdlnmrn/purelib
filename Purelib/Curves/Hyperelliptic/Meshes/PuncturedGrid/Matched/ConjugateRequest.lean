module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Integration.RectangularWholeSideMagnitude
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.Ring

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTraceRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest

open Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex

open Purelib.Riemann.Integration

open Purelib.Riemann.Periods

open Purelib.Topology.Polygon

public section

/-! Conjugate energy comparisons for matched subrectangle boundaries,
including all retained owner joins and endpoint chords. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateRequest

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

attribute [local congr] Purelib.Algebra.FiniteSum.Fin.sumFin_congr

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

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}
  {start : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner
    (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {firstDifferential secondDifferential : Differential genus}
    {firstSheet secondSheet : Fin 2}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation (MatchedSidePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation (AreaRequest)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

variable {leftBox rightBox : Purelib.Geometry.Rational.Box}
  {leftMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftRow : Fin leftMesh.partition.y.intervals.length} {rightRow : Fin rightMesh.partition.y.intervals.length}
  {height : Purelib.Data.Rat.Fraction.Rational} {depth : Nat}
  {side : Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh
    rightMesh leftRow rightRow height}
  {trace : side.Trace depth}

namespace MatchedSidePreparation.AreaRequest

variable {preparation : MatchedSidePreparation
  trace}
  {target : Coordinate} {floor : Nat}
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Data.Gaussian.Norm.Basic (normSq_conj)

/-- Gaussian conjugation distributes over the original ordered difference. -/
private theorem conjugate_sub (first last : Data.Gaussian.Basic.Canonical) : Data.Gaussian.Basic.conj (first -
  last) = Data.Gaussian.Basic.conj first - Data.Gaussian.Basic.conj last := by
  apply Data.Gaussian.Basic.ext
  · rfl
  · simp only [-eq_self, -iff_self, Data.Gaussian.Basic.conj, Data.Gaussian.Basic.sub_im]; ring1

/-- The paid horizontal matched-side request bounds the conjugate area discrepancy with its original endpoint chords
retained. -/
theorem conjugate_accurate (assembled : MatchedSidePreparation.AreaRequest preparation firstDifferential
  secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint -
      right.endpoint)) < target :=
by
  apply PairedTraceRequest.conjugate_accurate assembled.request (assembled.request_le.trans later) firstLeft firstRight
    secondLeft secondRight
    (trace.leftReadings firstLeft.anchors firstLeft.offsets) (trace.rightReadings firstRight.anchors firstRight.offsets)
    (trace.leftReadings secondLeft.anchors secondLeft.offsets) (trace.rightReadings secondRight.anchors
      secondRight.offsets) left right
  intro vertex
  rw [right.centered_eq]
  let first := GridPrimitiveAccuracy.atIndex
    assembled.firstGrid stage (assembled.first_le.trans later)
  let second := GridPrimitiveAccuracy.atIndex
    assembled.secondGrid stage (assembled.second_le.trans later)
  have firstBound := RectangularWholeSideMagnitude.matched_readings_magnitude first firstRight.anchors
    firstRight.offsets rightDomain.patch.cell_refines first.accurate.le trace vertex
  have secondBound := RectangularWholeSideMagnitude.matched_readings_magnitude second secondRight.anchors
    secondRight.offsets rightDomain.patch.cell_refines second.accurate.le trace vertex
  simp only [-eq_self, -iff_self, MatchedSidePreparation.wholeMagnitude,
    Aggregate.countCoordinate_eq]
  refine ⟨?_, secondBound.trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_right _ _)⟩
  change Data.Gaussian.Basic.Canonical.normSq (Data.Gaussian.Basic.conj ((trace.rightReadings
    firstRight.anchors firstRight.offsets).values vertex) -
    Data.Gaussian.Basic.conj ((trace.rightReadings firstRight.anchors firstRight.offsets).values 0)) ≤ _
  rw [←
    conjugate_sub,
    ← Data.Gaussian.Norm.Basic.normSq_eq_canonical, Data.Gaussian.Norm.Basic.normSq_conj,
    Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact firstBound.trans (Purelib.Data.Rat.Fraction.Order.Basic.le_max_left _ _)

/-- The actual horizontal subrectangle boundary areas and retained owner joins satisfy the original conjugate comparison
target after the exact endpoint correction. -/
theorem conjugate_boundary_accurate (assembled : MatchedSidePreparation.AreaRequest preparation firstDifferential
  secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    let leftValue := fun column row point => (⟨conj (firstLeft.anchors.alignedValue firstLeft.offsets column row point),
      secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩ : Stokes.PrimitivePoint)
    let rightValue := fun column row point => (⟨conj (firstRight.anchors.alignedValue firstRight.offsets column row
      point),
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (((side.leftArea leftValue depth + side.leftJoins leftValue) -
      (side.rightArea rightValue depth + side.rightJoins rightValue)) - (left.endpoint - right.endpoint)) < target := by
  intro leftValue rightValue
  have leftArea : left.originalArea = side.leftArea leftValue depth + side.leftJoins leftValue := by
    rw [left.originalArea_eq]
    have equal := trace.left_area leftValue
    unfold CenteredBilinearPath.area at equal ⊢
    simp only [-eq_self, -iff_self, trace.leftReadings_value]
    exact equal
  have rightArea : right.originalArea = side.rightArea rightValue depth + side.rightJoins rightValue := by
    rw [right.originalArea_eq]
    have equal := trace.right_area rightValue
    unfold CenteredBilinearPath.area at equal ⊢
    simp only [-eq_self, -iff_self, trace.rightReadings_value]
    exact equal
  have estimate :=
    conjugate_accurate
    assembled later firstLeft firstRight secondLeft secondRight left right
  rw [leftArea, rightArea] at estimate
  exact estimate

end MatchedSidePreparation.AreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateRequest
