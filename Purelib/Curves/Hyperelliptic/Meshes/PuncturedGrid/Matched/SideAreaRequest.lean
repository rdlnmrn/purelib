module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Polynomial.Rectangle.Accuracy.FragmentIndex
import Purelib.Riemann.Comparison.PrimitiveEdgeComparison
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
public import Purelib.Riemann.Readings.RectangularSeamBounds
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest
import Purelib.Riemann.Integration.RectangularWholeSideMagnitude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Nat.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Bounds
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
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames

public section

/-! A complete finite area request from cached common trace preparation.
Bounds and both differential contact banks are retained before numerical evaluation. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest

open Purelib.Algebra
open Purelib.Approximation
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib

attribute [local congr] FiniteSum.Fin.sumFin_congr

open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
      Meshes.PuncturedGridFaces.RegularFace
    bank}
  {firstModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames firstFace}
    {lastModels : Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank.FaceModels frames lastFace}
  {start : Gaussian.Basic.Canonical} {owner : Topology.SquareRootContinuationChain.Owner (curve.polynomial.eval start)}
  {leftEntry : Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry firstModels start owner} {rightEntry :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry lastModels start owner}
  {leftDomain : Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain firstModels leftEntry.sheet} {rightDomain :
    Hyperelliptic.Meshes.PuncturedGrid.Face.Periods.PeriodDomain lastModels rightEntry.sheet}
  {firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus} {firstSheet secondSheet
    : Fin 2}

variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {leftRow : Fin leftMesh.partition.y.intervals.length} {rightRow : Fin rightMesh.partition.y.intervals.length}
  {height : Fraction.Rational} {depth : Nat}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh rightMesh leftRow
    rightRow height}
  {trace : side.Trace depth}

namespace MatchedSidePreparation

/-- The retained whole-horizontal-side magnitude allowance from the original column count and boundary slope. -/
@[expose] def wholeMagnitude (count : Nat) (slope : Fraction.Rational) : Fraction.Rational :=
  2 * (slope + (Rational.Budget.Aggregate.countCoordinate count) ^ 2 * (2 * (4 + slope)))

set_option genInjectivity false in
/-- A paid complete comparison of the original matched horizontal traces.

Cache both differential bounds, original contact banks and a stage sufficient for every magnitude and accuracy request.
-/
structure AreaRequest
    (preparation :
      _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace)
    (firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus) (firstSheet
      secondSheet : Fin 2)
    (target : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The first differential's original primitive-overlap bounds. -/ firstBounds :
    Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator firstDifferential)
  /-- The second differential's original primitive-overlap bounds. -/ secondBounds :
    Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds lastFace.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator secondDifferential)
  /-- The first original grid accuracy request for the retained right domain. -/ firstGrid :
    Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy firstBounds rightDomain.steps 1
  /-- The second original grid accuracy request for the retained right domain. -/ secondGrid :
    Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy secondBounds rightDomain.steps 1
  /-- The first differential's actual original trace-contact bank. -/ firstBank :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => trace.point (trace.vertices.indexed vertex)) firstDifferential firstSheet
  /-- The second differential's actual original trace-contact bank. -/ secondBank :
    Hyperelliptic.Meshes.PuncturedGrid.TraceContactBanks.TraceContactBank leftEntry rightEntry leftDomain rightDomain
    (fun vertex => trace.point (trace.vertices.indexed vertex)) secondDifferential secondSheet
  /-- The first bank is exactly the contact cache of the retained original preparation. -/ firstBank_eq : firstBank =
    preparation.contacts firstDifferential firstSheet
  /-- The second bank is exactly the contact cache of the retained original preparation. -/ secondBank_eq : secondBank =
    preparation.contacts secondDifferential secondSheet
  /-- The paid paired-trace request using both original banks and their common magnitude bound. -/ request :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest firstBank secondBank
    (max (Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.wholeMagnitude
      leftMesh.boundaryColumns (Readings.RectangularSeamBounds.boundarySlope firstBounds))
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.wholeMagnitude
        leftMesh.boundaryColumns (Readings.RectangularSeamBounds.boundarySlope secondBounds))) target floor
  /-- The common sufficient stage for all original bounds and contact requests. -/ index : Nat
  /-- The original paired request is ready by the retained common stage. -/ request_le : request.index ≤ index
  /-- The first original grid accuracy request is ready by the retained stage. -/ first_le : firstGrid.index ≤ index
  /-- The second original grid accuracy request is ready by the retained stage. -/ second_le : secondGrid.index ≤ index

constructive_injectivity AreaRequest

namespace AreaRequest

variable {preparation :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- Prepare both original differential bounds and contact banks on the retained horizontal trace, then select a common
sufficient stage. -/
@[expose] def build (preparation :
  _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace)
    (firstDifferential secondDifferential : Hyperelliptic.Differentials.Basic.Differential genus) (firstSheet
      secondSheet : Fin 2)
    (target : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (floor : Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.AreaRequest preparation
      firstDifferential secondDifferential firstSheet secondSheet target floor := by
  let firstBounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build lastFace.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator firstDifferential)
  let secondBounds := Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds.build lastFace.clearance
    (Readings.PreparedPrimitiveSamples.differentialNumerator secondDifferential)
  let firstBank := preparation.contacts firstDifferential firstSheet
  let secondBank := preparation.contacts secondDifferential secondSheet
  have nonnegative : 0 ≤ Readings.RectangularSeamBounds.boundarySlope firstBounds :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.mul_nonneg_direct firstBounds.numeratorUpper_nonnegative
      firstBounds.inverseUpper_positive.le)) lastFace.cell.box.diagonalSq_nonneg
  let firstGrid := Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.build firstBounds rightDomain.steps 1
    (by decide)
  let secondGrid := Integration.RectangularPrimitiveAccuracy.GridPrimitiveAccuracy.build secondBounds rightDomain.steps
    1 (by decide)
  have magnitudeNonnegative : 0 ≤
    Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.wholeMagnitude
    leftMesh.boundaryColumns (Readings.RectangularSeamBounds.boundarySlope firstBounds) :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg nonnegative
      (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg (by decide) nonnegative))))
  let request := Hyperelliptic.Meshes.PuncturedGrid.Paired.TraceRequest.PairedTraceRequest.build firstBank secondBank _
    target
    (magnitudeNonnegative.trans (Fraction.Order.Basic.le_max_left _
      (Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.wholeMagnitude
      leftMesh.boundaryColumns (Readings.RectangularSeamBounds.boundarySlope secondBounds)))) positive floor
  exact ⟨firstBounds, secondBounds, firstGrid, secondGrid, firstBank, secondBank, rfl, rfl, request,
    max request.index (max firstGrid.index secondGrid.index), Purelib.Data.Nat.Order.le_max_left _ _,
    (Purelib.Data.Nat.Order.le_max_left _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _),
      (Purelib.Data.Nat.Order.le_max_right _ _).trans (Purelib.Data.Nat.Order.le_max_right _ _)⟩

/-- The original horizontal trace areas differ by less than the target after subtracting their actual endpoint
correction. -/
theorem accurate (assembled :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.AreaRequest preparation
  firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    Data.Gaussian.Norm.Basic.normSq ((left.originalArea - right.originalArea) - (left.endpoint - right.endpoint)) <
      target :=
open Purelib.Integration in by
  apply assembled.request.accurate (assembled.request_le.trans later) firstLeft firstRight secondLeft secondRight
    (trace.leftReadings firstLeft.anchors firstLeft.offsets) (trace.rightReadings firstRight.anchors firstRight.offsets)
    (trace.leftReadings secondLeft.anchors secondLeft.offsets) (trace.rightReadings secondRight.anchors
      secondRight.offsets) left right
  intro vertex
  rw [right.centered_eq]
  let first := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex assembled.firstGrid stage
    (assembled.first_le.trans later)
  let second := Polynomial.Rectangle.Accuracy.FragmentIndex.GridPrimitiveAccuracy.atIndex assembled.secondGrid stage
    (assembled.second_le.trans later)
  have firstBound := Integration.RectangularWholeSideMagnitude.matched_readings_magnitude first firstRight.anchors
    firstRight.offsets rightDomain.patch.cell_refines first.accurate.le trace vertex
  have secondBound := Integration.RectangularWholeSideMagnitude.matched_readings_magnitude second secondRight.anchors
    secondRight.offsets rightDomain.patch.cell_refines second.accurate.le trace vertex
  simp only [Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.wholeMagnitude,
    Rational.Budget.Aggregate.countCoordinate_eq]
  exact ⟨firstBound.trans (Fraction.Order.Basic.le_max_left _ _), secondBound.trans (Fraction.Order.Basic.le_max_right _
    _)⟩

/-- The original matched horizontal side areas and joins satisfy the paid comparison with the endpoint correction
retained. -/
theorem boundary_accurate (assembled :
  Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.AreaRequest preparation
  firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩)) :
    let leftValue := fun column row point => (⟨firstLeft.anchors.alignedValue firstLeft.offsets column row point,
      secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    let rightValue := fun column row point => (⟨firstRight.anchors.alignedValue firstRight.offsets column row point,
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (((side.leftArea leftValue depth + side.leftJoins leftValue) -
      (side.rightArea rightValue depth + side.rightJoins rightValue)) - (left.endpoint - right.endpoint)) < target := by
  intro leftValue rightValue
  have leftArea : left.originalArea = side.leftArea leftValue depth + side.leftJoins leftValue := by
    rw [left.originalArea_eq]
    have equal := trace.left_area leftValue
    unfold Periods.CenteredBilinearPath.area at equal ⊢
    simp only [trace.leftReadings_value]
    exact equal
  have rightArea : right.originalArea = side.rightArea rightValue depth + side.rightJoins rightValue := by
    rw [right.originalArea_eq]
    have equal := trace.right_area rightValue
    unfold Periods.CenteredBilinearPath.area at equal ⊢
    simp only [trace.rightReadings_value]
    exact equal
  have estimate := assembled.accurate later firstLeft firstRight secondLeft secondRight left right
  rw [leftArea, rightArea] at estimate
  exact estimate

end AreaRequest
end MatchedSidePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest

end
