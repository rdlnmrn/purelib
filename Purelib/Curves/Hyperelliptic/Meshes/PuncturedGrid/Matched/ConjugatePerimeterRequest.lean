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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalConjugateRequest
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

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

@[expose] public section

/-! Conjugate energy accuracy on actual cached subrectangle perimeters.
Owner jumps and endpoint corrections are retained in the comparison. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugatePerimeterRequest

open _root_.Purelib.Data.Gaussian.Basic (conj)

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

section
variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {height : Fraction.Rational}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedHorizontalSide leftMesh rightMesh
    (Fin.cast leftMesh.boundaryRows_eq (Fin.last leftMesh.boundaryRows))
    (Fin.cast rightMesh.boundaryRows_eq 0) height}
  {trace : side.Trace leftMesh.depth}
  {preparation : Hyperelliptic.Meshes.PuncturedGrid.Matched.SidePreparation.MatchedSidePreparation trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The actual top-minus-bottom perimeter difference satisfies the conjugate comparison target with both original
endpoint corrections retained. -/
theorem MatchedSidePreparation.AreaRequest.conjugate_top_sub_bottom_accurate
    (assembled : Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest.MatchedSidePreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩))
    (depthEq : leftMesh.depth = rightMesh.depth)
    (leftEdge : height = leftMesh.partition.y.intervals[Fin.cast leftMesh.boundaryRows_eq (Fin.last
      leftMesh.boundaryRows)].upper)
    (rightEdge : height = rightMesh.partition.y.intervals[Fin.cast rightMesh.boundaryRows_eq 0].lower)
    (leftAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly leftMesh
      (fun column row point => ⟨conj (firstLeft.anchors.alignedValue firstLeft.offsets column row point),
        secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩))
    (rightAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly rightMesh
      (fun column row point => ⟨conj (firstRight.anchors.alignedValue firstRight.offsets column row point),
        secondRight.anchors.alignedValue secondRight.offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq ((leftPerimeter.top - rightPerimeter.bottom) - (left.endpoint - right.endpoint))
      < target := by
  have estimate :=
    ConjugateRequest.MatchedSidePreparation.AreaRequest.conjugate_boundary_accurate
    assembled later firstLeft firstRight secondLeft secondRight left right
  dsimp only at estimate
  rw [side.left_boundary_eq_top _ leftAssembly leftPerimeter leftEdge] at estimate
  have depthReadback := congrArg (side.rightArea
    (fun column row point => (⟨conj (firstRight.anchors.alignedValue firstRight.offsets column row point),
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)))
        depthEq
  rw [depthReadback, side.right_boundary_eq_bottom _ rightAssembly rightPerimeter rightEdge] at estimate
  exact estimate

end

section
variable {leftBox rightBox : Rational.Box}
  {leftMesh : Meshes.RectangularObservationMesh.ObservationMesh leftDomain.cuts leftBox}
  {rightMesh : Meshes.RectangularObservationMesh.ObservationMesh rightDomain.cuts rightBox}
  {horizontal : Fraction.Rational}
  {side : Readings.RectangularMatchedObservationSides.ObservationMesh.MatchedVerticalSide leftMesh rightMesh
    (Fin.cast leftMesh.boundaryColumns_eq (Fin.last leftMesh.boundaryColumns))
    (Fin.cast rightMesh.boundaryColumns_eq 0) horizontal}
  {trace : side.Trace leftMesh.depth}
  {preparation : Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSidePreparation.MatchedVerticalSidePreparation
    trace}
  {target : Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

/-- The actual right-minus-left perimeter difference satisfies the conjugate comparison target with both original
endpoint corrections retained. -/
theorem MatchedVerticalSidePreparation.AreaRequest.conjugate_right_sub_left_accurate
    (assembled :
      Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest.MatchedVerticalSidePreparation.AreaRequest
      preparation firstDifferential secondDifferential firstSheet secondSheet target floor)
    {stage : Nat} (later : assembled.index ≤ stage)
    (firstLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain firstDifferential
      stage)
    (firstRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain firstDifferential
      stage)
    (secondLeft : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives leftDomain secondDifferential
      stage)
    (secondRight : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives rightDomain secondDifferential
      stage)
    (left : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.leftReadings firstLeft.anchors
      firstLeft.offsets).values vertex),
      (trace.leftReadings secondLeft.anchors secondLeft.offsets).values vertex⟩))
    (right : Periods.CenteredBilinearPath.Sample (fun vertex => ⟨conj ((trace.rightReadings firstRight.anchors
      firstRight.offsets).values vertex),
      (trace.rightReadings secondRight.anchors secondRight.offsets).values vertex⟩))
    (depthEq : leftMesh.depth = rightMesh.depth)
    (leftEdge : horizontal = leftMesh.partition.x.intervals[Fin.cast leftMesh.boundaryColumns_eq (Fin.last
      leftMesh.boundaryColumns)].upper)
    (rightEdge : horizontal = rightMesh.partition.x.intervals[Fin.cast rightMesh.boundaryColumns_eq 0].lower)
    (leftAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly leftMesh
      (fun column row point => ⟨conj (firstLeft.anchors.alignedValue firstLeft.offsets column row point),
        secondLeft.anchors.alignedValue secondLeft.offsets column row point⟩))
    (rightAssembly : Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly rightMesh
      (fun column row point => ⟨conj (firstRight.anchors.alignedValue firstRight.offsets column row point),
        secondRight.anchors.alignedValue secondRight.offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq ((leftPerimeter.right - rightPerimeter.left) - (left.endpoint - right.endpoint))
      < target := by
  have estimate :=
    VerticalConjugateRequest.MatchedVerticalSidePreparation.AreaRequest.conjugate_boundary_accurate
    assembled later firstLeft firstRight secondLeft secondRight left right
  dsimp only at estimate
  rw [side.left_boundary_eq_right _ leftAssembly leftPerimeter leftEdge] at estimate
  have depthReadback := congrArg (side.rightArea
    (fun column row point => (⟨conj (firstRight.anchors.alignedValue firstRight.offsets column row point),
      secondRight.anchors.alignedValue secondRight.offsets column row point⟩ : Topology.Polygon.Stokes.PrimitivePoint)))
        depthEq
  rw [depthReadback, side.right_boundary_eq_left _ rightAssembly rightPerimeter rightEdge] at estimate
  exact estimate

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.ConjugatePerimeterRequest
