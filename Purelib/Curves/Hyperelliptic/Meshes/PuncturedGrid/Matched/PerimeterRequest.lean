module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.RectangularMatchedObservationSides
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
import Purelib.Riemann.Integration.RectangularMatchedSideEndpoints
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Integration.RectangularMatchedPerimeter
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Topology.Polygon

@[expose] public section

/-! Whole-side accuracy on the two actual cached face perimeters. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest

open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods (PeriodDomain)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation (MatchedSidePreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation (MatchedVerticalSidePreparation)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {firstFace lastFace :
    RegularFace bank}
  {firstModels : FaceModels frames
    firstFace} {lastModels :
    FaceModels frames lastFace}

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Riemann.Periods.CenteredBilinearPath (Sample)
open Purelib.Riemann.Readings.RectangularPointReadings (PointReadings)
open Purelib.Riemann.Readings.RectangularSeamBounds (boundarySlope)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

section
variable {start : Purelib.Data.Gaussian.Basic.Canonical} {owner :
  Owner (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {firstDifferential secondDifferential : Differential genus}
    {firstSheet secondSheet : Fin 2}
  {leftBox rightBox : Purelib.Geometry.Rational.Box}
  {leftMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {height : Purelib.Data.Rat.Fraction.Rational}
  {side : MatchedHorizontalSide leftMesh
    rightMesh
    (Fin.cast leftMesh.boundaryRows_eq (Fin.last leftMesh.boundaryRows))
    (Fin.cast rightMesh.boundaryRows_eq 0) height}
  {trace : side.Trace leftMesh.depth}
  {preparation : MatchedSidePreparation trace}
  {target : Coordinate} {floor : Nat}

/-- The actual matched top-minus-bottom perimeter discrepancy, after its retained endpoint term, satisfies the original
whole-side target. -/
theorem MatchedSidePreparation.AreaRequest.top_sub_bottom_accurate
    (assembled : MatchedSidePreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors firstLeft.offsets).values
      vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩))
    (depthEq : leftMesh.depth = rightMesh.depth)
    (leftEdge : height = leftMesh.partition.y.intervals[Fin.cast leftMesh.boundaryRows_eq (Fin.last
      leftMesh.boundaryRows)].upper)
    (rightEdge : height = rightMesh.partition.y.intervals[Fin.cast rightMesh.boundaryRows_eq 0].lower)
    (leftAssembly : ObservationMesh.ClippedAssembly leftMesh
      (fun column row point => ⟨firstLeft.anchors.alignedValue firstLeft.offsets column row point,
        secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly rightMesh
      (fun column row point => ⟨firstRight.anchors.alignedValue firstRight.offsets column row point,
        secondRight.anchors.alignedValue secondRight.offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq ((leftPerimeter.top - rightPerimeter.bottom) - (left.endpoint -
      right.endpoint)) < target := by
  have estimate := assembled.boundary_accurate later firstLeft firstRight secondLeft secondRight left right
  dsimp only at estimate
  rw [side.left_boundary_eq_top _ leftAssembly leftPerimeter leftEdge] at estimate
  have depthReadback := congrArg (side.rightArea
    (fun column row point => (⟨firstRight.anchors.alignedValue firstRight.offsets column row point,
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Stokes.PrimitivePoint))) depthEq
  rw [depthReadback, side.right_boundary_eq_bottom _ rightAssembly rightPerimeter rightEdge] at estimate
  exact estimate

end

section
variable {start : Purelib.Data.Gaussian.Basic.Canonical} {owner :
  Owner (curve.polynomial.eval start)}
  {leftEntry : Entry firstModels start owner}
    {rightEntry : Entry lastModels start
    owner}
  {leftDomain : PeriodDomain firstModels leftEntry.sheet}
    {rightDomain : PeriodDomain lastModels
    rightEntry.sheet}
  {firstDifferential secondDifferential : Differential genus}
    {firstSheet secondSheet : Fin 2}
  {leftBox rightBox : Purelib.Geometry.Rational.Box}
  {leftMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Purelib.Riemann.Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {horizontal : Purelib.Data.Rat.Fraction.Rational}
  {side : MatchedVerticalSide leftMesh
    rightMesh
    (Fin.cast leftMesh.boundaryColumns_eq (Fin.last leftMesh.boundaryColumns))
    (Fin.cast rightMesh.boundaryColumns_eq 0) horizontal}
  {trace : side.Trace leftMesh.depth}
  {preparation :
    MatchedVerticalSidePreparation
    trace}
  {target : Coordinate} {floor : Nat}

/-- The actual matched right-minus-left perimeter discrepancy, after its retained endpoint term, satisfies the original
whole-side target. -/
theorem MatchedVerticalSidePreparation.AreaRequest.right_sub_left_accurate
    (assembled : MatchedVerticalSidePreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : PrimitiveData.DomainPrimitives leftDomain firstDifferential stage)
    (firstRight : PrimitiveData.DomainPrimitives rightDomain firstDifferential stage)
    (secondLeft : PrimitiveData.DomainPrimitives leftDomain secondDifferential stage)
    (secondRight : PrimitiveData.DomainPrimitives rightDomain secondDifferential stage)
    (left : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.leftReadings firstLeft.anchors firstLeft.offsets).values
      vertex,
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex => ⟨(trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex,
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩))
    (depthEq : leftMesh.depth = rightMesh.depth)
    (leftEdge : horizontal = leftMesh.partition.x.intervals[Fin.cast leftMesh.boundaryColumns_eq (Fin.last
      leftMesh.boundaryColumns)].upper)
    (rightEdge : horizontal = rightMesh.partition.x.intervals[Fin.cast rightMesh.boundaryColumns_eq 0].lower)
    (leftAssembly : ObservationMesh.ClippedAssembly leftMesh
      (fun column row point => ⟨firstLeft.anchors.alignedValue firstLeft.offsets column row point,
        secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly rightMesh
      (fun column row point => ⟨firstRight.anchors.alignedValue firstRight.offsets column row point,
        secondRight.anchors.alignedValue secondRight.offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq ((leftPerimeter.right - rightPerimeter.left) - (left.endpoint -
      right.endpoint)) < target := by
  have estimate := assembled.boundary_accurate later firstLeft firstRight secondLeft secondRight left right
  dsimp only at estimate
  rw [side.left_boundary_eq_right _ leftAssembly leftPerimeter leftEdge] at estimate
  have depthReadback := congrArg (side.rightArea
    (fun column row point => (⟨firstRight.anchors.alignedValue firstRight.offsets column row point,
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Stokes.PrimitivePoint))) depthEq
  rw [depthReadback, side.right_boundary_eq_left _ rightAssembly rightPerimeter rightEdge] at estimate
  exact estimate

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest
