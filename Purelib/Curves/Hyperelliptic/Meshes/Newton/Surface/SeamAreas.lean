module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MatchedSides
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
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
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Riemann.Integration.RectangularMatchedPerimeter

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly

open Purelib.Integration.Polynomial.Rectangle.Boundary

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

@[expose] public section

/-! Whole matched traces read back the actual face-assembly seam sides,
including each trace's model-owner joining edges. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open _root_.Purelib.Data.Gaussian.Basic (conj)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Periods.CenteredBilinearPath (area)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility (SurfaceCuts surfaceMeshes)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {observations : ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : SurfacePartitions observations grid}
  {surfaceCuts : SurfaceCuts partitions domains}
    {depth : Nat}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions
    (Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.MeshCompatibility.surfaceMeshes partitions domains surfaceCuts
    sheet depth) fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients}

/-- The coefficient combination of the retained aligned readings, shared by both owners of a seam. This is the value
specification of `EnergyAssembly`. -/
def seamValues (cache : LocalMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) :
    Fin (((domains.get position).domain sheet).steps + 1) →
      Fin (((domains.get position).domain sheet).steps + 1) → Data.Gaussian.Basic.Canonical → PrimitivePoint :=
  fun column row point =>
    ⟨sumFin (fun i => Data.Gaussian.Basic.conj (coefficients i) * Data.Gaussian.Basic.conj
      ((cache.atDomain position sheet i).anchors.alignedValue
      (cache.atDomain position sheet i).offsets column row point)),
      FiniteSum.Fin.sumFin (fun i => coefficients i * (cache.atDomain position sheet i).anchors.alignedValue
        (cache.atDomain position sheet i).offsets column row point)⟩

/-- The actual matched horizontal trace-area difference equals the original whole-face vertical seam contribution,
including retained model-owner joins. -/
theorem Perimeters.horizontal_trace_area (perimeters : FaceAssembly.Perimeters assemblies) (position : Fin
  grid.faces.regulars.length)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin (PieceIndices.rows (partitions.get
      position)))
    (trace : (MatchedSides.horizontalSeamSide energy position column row).Trace energy.depth) :
    CenteredBilinearPath.area (fun vertex => trace.leftValue
      (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) -
      CenteredBilinearPath.area (fun vertex => trace.rightValue
        (seamValues (sheet := sheet) cache coefficients position)
        (trace.vertices.indexed vertex)) =
      Assembly.verticalSeam (Perimeters.faceSides perimeters position) column row := by
  let above := PieceIndices.pieceIndex (partitions.get position) column row.succ
  let below := PieceIndices.pieceIndex (partitions.get position) column row.castSucc
  have leftArea : CenteredBilinearPath.area (fun vertex => trace.leftValue
    (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) = ((perimeters.get position).get above).bottom := by
    rw [trace.left_area, ← energy.mesh_depth position above]
    apply (MatchedSides.horizontalSeamSide energy position column row).left_boundary_eq_bottom _
      ((assemblies.get position).get above) ((perimeters.get position).get above)
    exact (PieceIndices.vertical_neighbor (partitions.get position) column row).trans
      ((energy.meshes.get position).entries.get above).y_first.symm
  have rightArea : CenteredBilinearPath.area (fun vertex => trace.rightValue
    (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) = ((perimeters.get position).get below).top := by
    rw [trace.right_area, ← energy.mesh_depth position below]
    apply (MatchedSides.horizontalSeamSide energy position column row).right_boundary_eq_top _
      ((assemblies.get position).get below) ((perimeters.get position).get below)
    exact ((energy.meshes.get position).entries.get below).y_last.symm
  rw [leftArea, rightArea]
  rfl

/-- The actual matched vertical trace-area difference equals the original whole-face horizontal seam contribution,
including retained model-owner joins. -/
theorem Perimeters.vertical_trace_area (perimeters : FaceAssembly.Perimeters assemblies) (position : Fin
  grid.faces.regulars.length)
    (column : Fin (PieceIndices.columns (partitions.get position))) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1))
    (trace : (MatchedSides.verticalSeamSide energy position column row).Trace energy.depth) :
    CenteredBilinearPath.area (fun vertex => trace.leftValue
      (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) -
      CenteredBilinearPath.area (fun vertex => trace.rightValue
        (seamValues (sheet := sheet) cache coefficients position)
        (trace.vertices.indexed vertex)) =
      Assembly.horizontalSeam (Perimeters.faceSides perimeters position) column row := by
  let left := PieceIndices.pieceIndex (partitions.get position) column.castSucc row
  let right := PieceIndices.pieceIndex (partitions.get position) column.succ row
  have leftArea : CenteredBilinearPath.area (fun vertex => trace.leftValue
    (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) = ((perimeters.get position).get left).right := by
    rw [trace.left_area, ← energy.mesh_depth position left]
    apply (MatchedSides.verticalSeamSide energy position column row).left_boundary_eq_right _
      ((assemblies.get position).get left) ((perimeters.get position).get left)
    exact ((energy.meshes.get position).entries.get left).x_last.symm
  have rightArea : CenteredBilinearPath.area (fun vertex => trace.rightValue
    (seamValues (sheet := sheet) cache coefficients position)
      (trace.vertices.indexed vertex)) = ((perimeters.get position).get right).left := by
    rw [trace.right_area, ← energy.mesh_depth position right]
    apply (MatchedSides.verticalSeamSide energy position column row).right_boundary_eq_left _
      ((assemblies.get position).get right) ((perimeters.get position).get right)
    exact (PieceIndices.horizontal_neighbor (partitions.get position) column row).trans
      ((energy.meshes.get position).entries.get right).x_first.symm
  rw [leftArea, rightArea]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
