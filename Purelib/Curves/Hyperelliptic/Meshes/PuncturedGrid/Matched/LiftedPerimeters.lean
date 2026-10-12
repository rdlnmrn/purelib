module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPreparations
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.SideAreaRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.VerticalSideAreaRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
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
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedFaceLocations
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedAreaRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest.MatchedSidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.PerimeterRequest.MatchedVerticalSidePreparation

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.RectangularObservationAssembly

open Purelib.Topology.Polygon

@[expose] public section

/-! The lifted reversal supplies physical adjacency for cached perimeter bounds. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedSides (HorizontalCrossing VerticalCrossing)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Readings.RectangularMatchedObservationSides.ObservationMesh (MatchedHorizontalSide
  MatchedVerticalSide)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {domains :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
  {cuts : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains sheet}
    {target : Purelib.Data.Rat.Fraction.Rational}
  {mesh : Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {firstPosition : Fin faces.regulars.length} {firstSheet : Fin 2}

variable {request : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet
  => Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet
  coarseDepth) fixed target}

open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)

namespace HorizontalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The retained lifted reversal identifies the original horizontal crossing's two physical box boundaries. -/
theorem adjacent (joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper) :
    faces.regulars[firstPosition.val].cell.box.yUpper = faces.regulars[nextPosition.val].cell.box.yLower := by
  have equal := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    (vertices.coordinate edge.start).im) joined.reversed
  change (vertices.coordinate joined.crossing.next.located.lifted.quad.first).im =
    (vertices.coordinate first.lifted.quad.fourth).im at equal
  rw [joined.crossing.next.located.lifted.coordinates.1, first.lifted.coordinates.2.2.2] at equal
  exact equal.symm

/-- The original horizontal crossing request controls its cached perimeter difference after subtracting the actual
retained endpoint correction.

Both original face assemblies and centered samples are consumed at the same paid numerical stage. -/
theorem AreaRequest.perimeter_accurate
    {joined : LiftedSides.HorizontalCrossing request first nextPosition firstUpper lastUpper}
    {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor : Nat}
    (allocated : HorizontalCrossing.AreaRequest joined
      (PeriodMatrix.standardDifferential i) (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) (later : allocated.accuracy.index ≤ stage)
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings (cache.atDomain firstPosition firstSheet i).anchors
          (cache.atDomain firstPosition firstSheet i).offsets).values vertex,
        (allocated.trace.leftReadings (cache.atDomain firstPosition firstSheet j).anchors
          (cache.atDomain firstPosition firstSheet j).offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors
          (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets).values vertex,
        (allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets).values vertex⟩))
    (leftAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get firstSheet).meshes.entries.get firstPosition)
      (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue (cache.atDomain firstPosition firstSheet
          i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue (cache.atDomain firstPosition firstSheet
            j).offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get (joined.crossing.next.sheet)).meshes.entries.get nextPosition)
      (fun column row point =>
        ⟨(cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors.alignedValue (cache.atDomain nextPosition
          (joined.crossing.next.sheet) i).offsets column row point,
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue (cache.atDomain nextPosition
            (joined.crossing.next.sheet) j).offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq
      ((leftPerimeter.top - rightPerimeter.bottom) - (left.endpoint - right.endpoint)) < tolerance := by
  exact AreaRequest.top_sub_bottom_accurate
    allocated.accuracy later
    (cache.atDomain firstPosition firstSheet i) (cache.atDomain nextPosition joined.crossing.next.sheet i)
    (cache.atDomain firstPosition firstSheet j) (cache.atDomain nextPosition joined.crossing.next.sheet j)
    left right (by rw [request.mesh_depth, request.mesh_depth])
    ((request.entries.get firstSheet).meshes.entries.get firstPosition).y_last.symm
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters.HorizontalCrossing.adjacent joined |>.trans
      ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).y_first.symm)
    leftAssembly rightAssembly leftPerimeter rightPerimeter

end HorizontalCrossing

namespace VerticalCrossing
variable {first : mesh.LocatedFace firstPosition firstSheet} {nextPosition : Fin faces.regulars.length}
  {firstUpper lastUpper : Bool}

/-- The retained lifted reversal identifies the original vertical crossing's two physical box boundaries. -/
theorem adjacent (joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper) :
    faces.regulars[firstPosition.val].cell.box.xUpper = faces.regulars[nextPosition.val].cell.box.xLower := by
  have equal := congrArg (fun edge : Stokes.OrientedEdge vertices.count =>
    (vertices.coordinate edge.finish).re) joined.reversed
  change (vertices.coordinate joined.crossing.next.located.lifted.quad.first).re =
    (vertices.coordinate first.lifted.quad.second).re at equal
  rw [joined.crossing.next.located.lifted.coordinates.1, first.lifted.coordinates.2.1] at equal
  exact equal.symm

/-- The original vertical crossing request controls its cached perimeter difference after subtracting the actual
retained endpoint correction.

Both original face assemblies and centered samples are consumed at the same paid numerical stage. -/
theorem AreaRequest.perimeter_accurate
    {joined : LiftedSides.VerticalCrossing request first nextPosition firstUpper lastUpper}
    {i j : Fin genus} {firstParent secondParent : Fin 2} {tolerance : Fraction.Rational} {floor : Nat}
    (allocated : VerticalCrossing.AreaRequest joined
      (PeriodMatrix.standardDifferential i) (PeriodMatrix.standardDifferential j)
      firstParent secondParent tolerance floor)
    {stage : Nat} (cache : RegularMeshes.Numerics domains stage) (later : allocated.accuracy.index ≤ stage)
    (left : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.leftReadings (cache.atDomain firstPosition firstSheet i).anchors
          (cache.atDomain firstPosition firstSheet i).offsets).values vertex,
        (allocated.trace.leftReadings (cache.atDomain firstPosition firstSheet j).anchors
          (cache.atDomain firstPosition firstSheet j).offsets).values vertex⟩))
    (right : CenteredBilinearPath.Sample (fun vertex =>
      ⟨(allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors
          (cache.atDomain nextPosition (joined.crossing.next.sheet) i).offsets).values vertex,
        (allocated.trace.rightReadings (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).offsets).values vertex⟩))
    (leftAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get firstSheet).meshes.entries.get firstPosition)
      (fun column row point =>
        ⟨(cache.atDomain firstPosition firstSheet i).anchors.alignedValue (cache.atDomain firstPosition firstSheet
          i).offsets column row point,
          (cache.atDomain firstPosition firstSheet j).anchors.alignedValue (cache.atDomain firstPosition firstSheet
            j).offsets column row point⟩))
    (rightAssembly : ObservationMesh.ClippedAssembly
      ((request.entries.get (joined.crossing.next.sheet)).meshes.entries.get nextPosition)
      (fun column row point =>
        ⟨(cache.atDomain nextPosition (joined.crossing.next.sheet) i).anchors.alignedValue (cache.atDomain nextPosition
          (joined.crossing.next.sheet) i).offsets column row point,
          (cache.atDomain nextPosition (joined.crossing.next.sheet) j).anchors.alignedValue (cache.atDomain nextPosition
            (joined.crossing.next.sheet) j).offsets column row point⟩))
    (leftPerimeter : leftAssembly.Perimeter) (rightPerimeter : rightAssembly.Perimeter) :
    Data.Gaussian.Norm.Basic.normSq
      ((leftPerimeter.right - rightPerimeter.left) - (left.endpoint - right.endpoint)) < tolerance := by
  exact AreaRequest.right_sub_left_accurate
    allocated.accuracy later
    (cache.atDomain firstPosition firstSheet i) (cache.atDomain nextPosition joined.crossing.next.sheet i)
    (cache.atDomain firstPosition firstSheet j) (cache.atDomain nextPosition joined.crossing.next.sheet j)
    left right (by rw [request.mesh_depth, request.mesh_depth])
    ((request.entries.get firstSheet).meshes.entries.get firstPosition).x_last.symm
    (Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters.VerticalCrossing.adjacent joined |>.trans
      ((request.entries.get joined.crossing.next.sheet).meshes.entries.get nextPosition).x_first.symm)
    leftAssembly rightAssembly leftPerimeter rightPerimeter

end VerticalCrossing

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.LiftedPerimeters
