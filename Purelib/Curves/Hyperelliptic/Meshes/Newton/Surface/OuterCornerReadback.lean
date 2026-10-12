module
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
public import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
import Purelib.Riemann.Readings.RectangularOuterCornerReadings
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
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
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularPointReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners

open Purelib.Geometry

open Purelib.Geometry.Rectangle.Partition

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularExteriorCornerOwners

open Purelib.Riemann.Readings.RectangularOuterCornerReadings

open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy

open Purelib.Riemann.Topology

open Purelib.Topology.Polygon.Stokes

@[expose] public section

/-! Outer corners of the complete observation-cut surface read the same
primitive cache as the fixed four-corner bank used by period triangles. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly (Perimeters)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)

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
  {partitions : SurfacePartitions observations grid} {coarse :
    SurfaceMeshes partitions domains sheet}
  {fixed : Preflights domains sheet} {error :
    Rational}
  {energy : SurfaceRequest partitions coarse fixed error}
  {stage : Nat} {cache : Numerics domains
    stage} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}
  {assemblies : ExteriorRequest.Assemblies energy
    cache coefficients} {perimeters : Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

namespace OuterCorners

open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open _root_.Purelib.Data.Gaussian.Basic (conj)

/-- The actual retained exterior vertex owner at one extreme corner of the complete original surface partition. -/
def owner (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error) (position : Fin
  grid.faces.regulars.length)
    (right above : Bool) : RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry :=
  let partition := partitions.get position
  let piece := PieceIndices.pieceIndex partition (if right then Fin.last (PieceIndices.columns partition) else 0) (if
    above then Fin.last (PieceIndices.rows partition) else 0)
  RectangularExteriorCornerOwners.exteriorCornerOwner ((energy.meshes.get position).entries.get piece) right above

/-- The selected exterior owner lies at the corresponding corner of the original regular face box. -/
theorem owner_point (right above : Bool) :
    (owner energy position right
      above).point =
      PreparedRectangleCuts.corner (grid.faces.regulars[position.val]'position.isLt).cell.box right above := by
  unfold owner
  rw [RectangularExteriorCornerOwners.exteriorCornerOwner_point]
  cases right <;> cases above <;> rw [PieceIndices.piece_box (partitions.get position)] <;>
    apply Data.Gaussian.Basic.ext
  · exact (partitions.get position).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get position))
      0).isLt
  · exact (partitions.get position).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get position))
      0).isLt
  · exact (partitions.get position).cuts.x.first_lower (Fin.cast (PieceIndices.columns_eq (partitions.get position))
      0).isLt
  · exact (partitions.get position).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get position))
  · exact (partitions.get position).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get position))
  · exact (partitions.get position).cuts.y.first_lower (Fin.cast (PieceIndices.rows_eq (partitions.get position))
      0).isLt
  · exact (partitions.get position).cuts.x.last_upper _ (PieceIndices.columns_eq (partitions.get position))
  · exact (partitions.get position).cuts.y.last_upper _ (PieceIndices.rows_eq (partitions.get position))

/-- The acquired primitive pair at the selected extreme corner of the original assembled surface. -/
def value (face : FaceAssembly perimeters position) (right above : Bool) : PrimitivePoint :=
  let partition := partitions.get position
  let corners := face.corners (if right then Fin.last (PieceIndices.columns partition) else 0) (if above then Fin.last
    (PieceIndices.rows partition) else 0)
  if right then (if above then corners.upperRight else corners.lowerRight)
  else (if above then corners.upperLeft else corners.lowerLeft)

/-- The acquired extreme corner reads the actual primitive cache of its retained exterior vertex owner. -/
theorem value_eq_owner (face : FaceAssembly perimeters position) (right above : Bool) :
    value face right above =
      let vertex := owner energy position
        right above
      SeamAreas.seamValues (sheet := sheet) cache coefficients position vertex.column vertex.row vertex.point := by
  cases right <;> cases above <;> dsimp only
    [value] <;> rw [face.corners_eq]
  · exact (ClippedAssembly.exterior_corners
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) 0 0))).1
  · exact (ClippedAssembly.exterior_corners
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) 0 (Fin.last (PieceIndices.rows
        (partitions.get position)))))).2.2.1
  · exact (ClippedAssembly.exterior_corners
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns
        (partitions.get position))) 0))).2.1
  · exact (ClippedAssembly.exterior_corners
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns
        (partitions.get position)))
      (Fin.last (PieceIndices.rows (partitions.get position)))))).2.2.2

/-- The original four-corner index selected by the horizontal and vertical side flags. -/
def index (right above : Bool) : Fin 4 := if right then (if above then 2 else 1) else (if above then 3 else 0)

/-- The four-corner index selects exactly the corresponding physical rectangle corner. -/
theorem index_point (box : Rational.Box) (right above : Bool) :
    FaceCorners.point box (index right
      above) = PreparedRectangleCuts.corner box right above := by
  cases right <;> cases above <;> rfl

/-- Each actual basis reading at the original exterior owner equals its retained four-corner cache entry. -/
theorem basis_value (basis : Fin genus) (right above : Bool) :
    let vertex := owner energy position
      right above
    (cache.atDomain position sheet basis).anchors.alignedValue (cache.atDomain position sheet basis).offsets
      vertex.column vertex.row vertex.point = (cache.atDomain position sheet basis).corners.values
        (index right above) :=
  PointReadings.outer_corner_value (cache.atDomain position sheet basis).corners
    ((domains.get position).domain sheet).patch.cell_refines
      (owner energy position right above)
    (index right above) right above
      (owner_point right above)
      (index_point _ right above)

/-- The conjugate and direct coefficient sums of the original retained four-corner basis cache. -/
def cachedValue (cache : LocalMeshes.Numerics domains stage) (coefficients :
  LinearAlgebra.Gaussian.Energy.GaussianVector genus)
    (position : Fin grid.faces.regulars.length) (sheet : Fin 2) (corner : Fin 4) : PrimitivePoint :=
  ⟨sumFin (fun basis => Data.Gaussian.Basic.conj (coefficients basis) * Data.Gaussian.Basic.conj
    ((cache.atDomain position sheet basis).corners.values corner)),
    FiniteSum.Fin.sumFin (fun basis => coefficients basis * (cache.atDomain position sheet basis).corners.values
      corner)⟩

/-- The acquired outer surface corner equals the coefficient pair computed from the original retained four-corner cache.
-/
theorem value_eq_cached (face : FaceAssembly perimeters position) (right above : Bool) :
    value face right above =
      cachedValue cache coefficients
      position sheet (index right above) :=
      by
  rw [value_eq_owner]
  apply congrArg₂ PrimitivePoint.mk
  · apply FiniteSum.Fin.sumFin_congr
    intro basis
    exact congrArg (fun reading => Data.Gaussian.Basic.conj (coefficients basis) *
      Data.Gaussian.Basic.conj reading)
      (basis_value (energy := energy) basis
      right above)
  · apply FiniteSum.Fin.sumFin_congr
    intro basis
    exact congrArg (fun reading => coefficients basis * reading)
      (basis_value (energy := energy) basis
      right above)

end OuterCorners
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.OuterCornerReadback
