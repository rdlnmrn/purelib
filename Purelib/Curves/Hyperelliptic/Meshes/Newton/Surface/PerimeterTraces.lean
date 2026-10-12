module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Integration.RectangularExteriorCornerOwners
import Purelib.Riemann.Integration.RectangularOwnedTriangulation
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas
public import Purelib.Riemann.Paths.RectangularOwnedPerimeterTraces
import Init.Data.Fin.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly

open Purelib.Data.Vector

open Purelib.Integration.Path

open Purelib.Integration.Path.JoinedTrace

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.RectangularExteriorCornerOwners

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.RectangularPerimeterTraces

open Purelib.Riemann.Topology

open Purelib.Topology.Polygon

@[expose] public section

/-! Whole regular-face perimeter traces concatenate the retained piece
traces with their actual model owners and every joining edge. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest (Assemblies)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.SeamAreas (seamValues)

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
    cache coefficients} {perimeters : Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
    assemblies}
  {position : Fin grid.faces.regulars.length}

open Purelib.Riemann.Integration.RectangularOwnedTriangulation (OwnedVertex)
open Purelib.Riemann.Paths.RectangularPerimeterTraces (PerimeterTraces)

open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_sub)

/-- The dependent bank of perimeter traces on every actual original observation-cut piece. -/
def PiecePerimeterTraces (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) :=
  Data.Vector.DependentVector (fun piece : Fin (partitions.get position).cuts.boxes.length =>
    RectangularPerimeterTraces.PerimeterTraces ((energy.meshes.get position).entries.get piece))

/-- The actual owned bottom trace of each original boundary piece. -/
def PiecePerimeterTraces.bottomPieces (pieces :
  PiecePerimeterTraces energy position)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) : JoinedTrace.VertexTrace
      (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry) :=
  RectangularOwnedPerimeterTraces.bottomOwned (pieces.get (PieceIndices.pieceIndex (partitions.get position) column 0))

/-- The actual owned top trace of each original boundary piece. -/
def PiecePerimeterTraces.topPieces (pieces :
  PiecePerimeterTraces energy position)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) : JoinedTrace.VertexTrace
      (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry) :=
  RectangularOwnedPerimeterTraces.topOwned (pieces.get (PieceIndices.pieceIndex (partitions.get position) column
    (Fin.last (PieceIndices.rows (partitions.get position)))))

/-- The actual owned left trace of each original boundary piece. -/
def PiecePerimeterTraces.leftPieces (pieces :
  PiecePerimeterTraces energy position)
    (column : Fin ((PieceIndices.rows (partitions.get position)) + 1)) : JoinedTrace.VertexTrace
      (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry) :=
  RectangularOwnedPerimeterTraces.leftOwned (pieces.get (PieceIndices.pieceIndex (partitions.get position) 0 column))

/-- The actual owned right trace of each original boundary piece. -/
def PiecePerimeterTraces.rightPieces (pieces :
  PiecePerimeterTraces energy position)
    (column : Fin ((PieceIndices.rows (partitions.get position)) + 1)) : JoinedTrace.VertexTrace
      (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry) :=
  RectangularOwnedPerimeterTraces.rightOwned (pieces.get (PieceIndices.pieceIndex (partitions.get position) (Fin.last
    (PieceIndices.columns (partitions.get position))) column))

set_option genInjectivity false in
/-- The four complete boundary traces of the original regular face.

Each trace concatenates the retained piece traces with their actual model vertex owners and every intervening joining
edge. -/
structure FacePerimeterTraces (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error)
    (position : Fin grid.faces.regulars.length) where
  /-- The original dependent bank of all retained piece perimeter traces. -/ pieces :
    PiecePerimeterTraces energy position
  /-- The cached complete bottom boundary trace with original vertex owners and joining edges. -/ bottom :
    JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
  /-- The retained bottom trace is exactly the concatenation of the actual original piece traces. -/ bottom_eq : bottom
    = VertexTrace.concatenate pieces.bottomPieces
  /-- The cached complete top boundary trace with original vertex owners and joining edges. -/ top :
    JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
  /-- The retained top trace is exactly the concatenation of the actual original piece traces. -/ top_eq : top =
    VertexTrace.concatenate pieces.topPieces
  /-- The cached complete left boundary trace with original vertex owners and joining edges. -/ left :
    JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
  /-- The retained left trace is exactly the concatenation of the actual original piece traces. -/ left_eq : left =
    VertexTrace.concatenate pieces.leftPieces
  /-- The cached complete right boundary trace with original vertex owners and joining edges. -/ right :
    JoinedTrace.VertexTrace (RectangularOwnedTriangulation.OwnedVertex ((domains.get position).domain sheet).geometry)
  /-- The retained right trace is exactly the concatenation of the actual original piece traces. -/ right_eq : right =
    VertexTrace.concatenate pieces.rightPieces

constructive_injectivity FacePerimeterTraces

namespace FacePerimeterTraces

/-- Build each original piece perimeter once and concatenate the four actual boundary rows while retaining their exact
readbacks. -/
def build (energy : NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed error) (position : Fin
  grid.faces.regulars.length) :
    Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy position :=
  let pieces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.PiecePerimeterTraces energy position :=
    DependentVector.ofFn fun piece =>
    PerimeterTraces.build ((energy.meshes.get position).entries.get piece)
  ⟨pieces, VertexTrace.concatenate pieces.bottomPieces, rfl, VertexTrace.concatenate pieces.topPieces, rfl,
    VertexTrace.concatenate pieces.leftPieces, rfl, VertexTrace.concatenate pieces.rightPieces, rfl⟩

/-- The first owner of each original bottom piece trace reads its acquired lower-left corner. -/
private theorem bottom_first (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.columns (partitions.get
      position)) + 1)) :
    let owner := (traces.pieces.bottomPieces column).first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners column 0).lowerLeft := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.bottomOwned_first (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) column 0))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) column 0))).1.symm

/-- The last owner of each original bottom piece trace reads its acquired lower-right corner. -/
private theorem bottom_last (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.columns (partitions.get
      position)) + 1)) :
    let owner := (traces.pieces.bottomPieces column).last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners column 0).lowerRight := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.bottomOwned_last (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) column 0))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) column 0))).2.1.symm

/-- The complete bottom trace area is the sum of its actual original piece areas and every intervening corner-joining
area. -/
theorem bottom_area (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    traces.bottom.area (fun owner => SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column
      owner.row owner.point) =
      FiniteSum.Fin.sumFin (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
        (Perimeters.faceSides perimeters position column 0).bottom) +
      FiniteSum.Fin.sumFin (fun column : Fin (PieceIndices.columns (partitions.get position)) =>
        Stokes.edgeArea (face.corners column.castSucc 0).lowerRight (face.corners column.succ 0).lowerLeft) := by
  rw [traces.bottom_eq, VertexTrace.concatenate_area, VertexTrace.joiningArea_ofFn]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact RectangularOwnedPerimeterTraces.bottomOwned_area (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
      position) column 0))
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position)
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) column 0))
      ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column 0))
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact congrArg₂ Stokes.edgeArea (traces.bottom_last face column.castSucc) (traces.bottom_first face column.succ)

/-- The first owner of each original top piece trace reads its acquired upper-left corner. -/
private theorem top_first (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.columns (partitions.get
      position)) + 1)) :
    let owner := (traces.pieces.topPieces column).first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners column (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.topOwned_first (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) column (Fin.last (PieceIndices.rows (partitions.get position)))))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) column (Fin.last (PieceIndices.rows (partitions.get position)))))).2.2.1.symm

/-- The last owner of each original top piece trace reads its acquired upper-right corner. -/
private theorem top_last (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.columns (partitions.get
      position)) + 1)) :
    let owner := (traces.pieces.topPieces column).last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners column (Fin.last (PieceIndices.rows (partitions.get position)))).upperRight := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.topOwned_last (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) column (Fin.last (PieceIndices.rows (partitions.get position)))))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) column (Fin.last (PieceIndices.rows (partitions.get position)))))).2.2.2.symm

/-- The complete top trace area is the sum of its actual original piece areas and every intervening corner-joining area.
-/
theorem top_area (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    traces.top.area (fun owner => SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column
      owner.row owner.point) =
      FiniteSum.Fin.sumFin (fun column : Fin ((PieceIndices.columns (partitions.get position)) + 1) =>
        (Perimeters.faceSides perimeters position column (Fin.last (PieceIndices.rows (partitions.get position)))).top)
        +
      FiniteSum.Fin.sumFin (fun column : Fin (PieceIndices.columns (partitions.get position)) =>
        Stokes.edgeArea (face.corners column.castSucc (Fin.last (PieceIndices.rows (partitions.get
          position)))).upperRight (face.corners column.succ (Fin.last (PieceIndices.rows (partitions.get
          position)))).upperLeft) := by
  rw [traces.top_eq, VertexTrace.concatenate_area, VertexTrace.joiningArea_ofFn]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact RectangularOwnedPerimeterTraces.topOwned_area (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
      position) column (Fin.last (PieceIndices.rows (partitions.get position)))))
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position)
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) column (Fin.last
        (PieceIndices.rows (partitions.get position)))))
      ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column (Fin.last
        (PieceIndices.rows (partitions.get position)))))
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact congrArg₂ Stokes.edgeArea (traces.top_last face column.castSucc) (traces.top_first face column.succ)

/-- The first owner of each original left piece trace reads its acquired lower-left corner. -/
private theorem left_first (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.rows (partitions.get position))
      + 1)) :
    let owner := (traces.pieces.leftPieces column).first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 column).lowerLeft := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.leftOwned_first (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) 0 column))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) 0 column))).1.symm

/-- The last owner of each original left piece trace reads its acquired upper-left corner. -/
private theorem left_last (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.rows (partitions.get position))
      + 1)) :
    let owner := (traces.pieces.leftPieces column).last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 column).upperLeft := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.leftOwned_last (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) 0 column))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) 0 column))).2.2.1.symm

/-- The complete left trace area is the sum of its actual original piece areas and every intervening corner-joining
area. -/
theorem left_area (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    traces.left.area (fun owner => SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column
      owner.row owner.point) =
      FiniteSum.Fin.sumFin (fun column : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
        (Perimeters.faceSides perimeters position 0 column).left) +
      FiniteSum.Fin.sumFin (fun column : Fin (PieceIndices.rows (partitions.get position)) =>
        Stokes.edgeArea (face.corners 0 column.castSucc).upperLeft (face.corners 0 column.succ).lowerLeft) := by
  rw [traces.left_eq, VertexTrace.concatenate_area, VertexTrace.joiningArea_ofFn]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact RectangularOwnedPerimeterTraces.leftOwned_area (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
      position) 0 column))
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position)
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) 0 column))
      ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) 0 column))
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact congrArg₂ Stokes.edgeArea (traces.left_last face column.castSucc) (traces.left_first face column.succ)

/-- The first owner of each original right piece trace reads its acquired lower-right corner. -/
private theorem right_first (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.rows (partitions.get position))
      + 1)) :
    let owner := (traces.pieces.rightPieces column).first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) column).lowerRight := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.rightOwned_first (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) (Fin.last (PieceIndices.columns (partitions.get position))) column))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) (Fin.last (PieceIndices.columns (partitions.get position))) column))).2.1.symm

/-- The last owner of each original right piece trace reads its acquired upper-right corner. -/
private theorem right_last (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position)
    (face : FaceAssembly perimeters position) (column : Fin ((PieceIndices.rows (partitions.get position))
      + 1)) :
    let owner := (traces.pieces.rightPieces column).last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) column).upperRight := by
  rw [face.corners_eq]
  exact (RectangularOwnedPerimeterTraces.rightOwned_last (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
    position) (Fin.last (PieceIndices.columns (partitions.get position))) column))
    (SeamAreas.seamValues (sheet := sheet) cache coefficients position)).trans
      (ClippedAssembly.exterior_corners ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get
        position) (Fin.last (PieceIndices.columns (partitions.get position))) column))).2.2.2.symm

/-- The complete right trace area is the sum of its actual original piece areas and every intervening corner-joining
area. -/
theorem right_area (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    traces.right.area (fun owner => SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column
      owner.row owner.point) =
      FiniteSum.Fin.sumFin (fun column : Fin ((PieceIndices.rows (partitions.get position)) + 1) =>
        (Perimeters.faceSides perimeters position (Fin.last (PieceIndices.columns (partitions.get position)))
        column).right) +
      FiniteSum.Fin.sumFin (fun column : Fin (PieceIndices.rows (partitions.get position)) =>
        Stokes.edgeArea (face.corners (Fin.last (PieceIndices.columns (partitions.get position)))
          column.castSucc).upperRight (face.corners (Fin.last (PieceIndices.columns (partitions.get position)))
          column.succ).lowerRight) := by
  rw [traces.right_eq, VertexTrace.concatenate_area, VertexTrace.joiningArea_ofFn]
  apply congrArg₂ (fun a b : Data.Gaussian.Basic.Canonical => a + b)
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact RectangularOwnedPerimeterTraces.rightOwned_area (traces.pieces.get (PieceIndices.pieceIndex (partitions.get
      position) (Fin.last (PieceIndices.columns (partitions.get position))) column))
      (SeamAreas.seamValues (sheet := sheet) cache coefficients position)
      ((assemblies.get position).get (PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns
        (partitions.get position))) column))
      ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) (Fin.last (PieceIndices.columns
        (partitions.get position))) column))
  · apply FiniteSum.Fin.sumFin_congr
    intro column
    exact congrArg₂ Stokes.edgeArea (traces.right_last face column.castSucc) (traces.right_first face column.succ)

/-- The first owner of the complete bottom trace reads the original exterior lower-left corner. -/
theorem bottom_first_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position) (face : FaceAssembly perimeters position) :
    let owner := traces.bottom.first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 0).lowerLeft := by
  dsimp only
  rw [traces.bottom_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  exact traces.bottom_first face 0

/-- The last owner of the complete bottom trace reads the original exterior lower-right corner. -/
theorem bottom_last_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position) (face : FaceAssembly perimeters position) :
    let owner := traces.bottom.last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) 0).lowerRight := by
  dsimp only
  rw [traces.bottom_eq, VertexTrace.concatenate_last]
  exact traces.bottom_last face (Fin.last (PieceIndices.columns (partitions.get position)))

/-- The first owner of the complete top trace reads the original exterior upper-left corner. -/
theorem top_first_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let owner := traces.top.first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft := by
  dsimp only
  rw [traces.top_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  exact traces.top_first face 0

/-- The last owner of the complete top trace reads the original exterior upper-right corner. -/
theorem top_last_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let owner := traces.top.last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last (PieceIndices.rows
        (partitions.get position)))).upperRight := by
  dsimp only
  rw [traces.top_eq, VertexTrace.concatenate_last]
  exact traces.top_last face (Fin.last (PieceIndices.columns (partitions.get position)))

/-- The first owner of the complete left trace reads the original exterior lower-left corner. -/
theorem left_first_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let owner := traces.left.first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 0).lowerLeft := by
  dsimp only
  rw [traces.left_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  exact traces.left_first face 0

/-- The last owner of the complete left trace reads the original exterior upper-left corner. -/
theorem left_last_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let owner := traces.left.last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners 0 (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft := by
  dsimp only
  rw [traces.left_eq, VertexTrace.concatenate_last]
  exact traces.left_last face (Fin.last (PieceIndices.rows (partitions.get position)))

/-- The first owner of the complete right trace reads the original exterior lower-right corner. -/
theorem right_first_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces
  energy position) (face : FaceAssembly perimeters position) :
    let owner := traces.right.first
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) 0).lowerRight := by
  dsimp only
  rw [traces.right_eq, VertexTrace.concatenate, VertexTrace.glue_first]
  exact traces.right_first face 0

/-- The last owner of the complete right trace reads the original exterior upper-right corner. -/
theorem right_last_value (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let owner := traces.right.last
    SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row owner.point =
      (face.corners (Fin.last (PieceIndices.columns (partitions.get position))) (Fin.last (PieceIndices.rows
        (partitions.get position)))).upperRight := by
  dsimp only
  rw [traces.right_eq, VertexTrace.concatenate_last]
  exact traces.right_last face (Fin.last (PieceIndices.rows (partitions.get position)))

/-- The assembled original exterior area equals the signed areas of its four complete retained boundary traces,
including all joining edges. -/
theorem exterior_eq (traces : Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces.FacePerimeterTraces energy
  position) (face : FaceAssembly perimeters position) :
    let values := fun owner => SeamAreas.seamValues (sheet := sheet) cache coefficients position owner.column owner.row
      owner.point
    face.exterior = traces.bottom.area values + traces.right.area values - traces.top.area values - traces.left.area
      values := by
  dsimp only
  rw [face.exterior_eq, traces.bottom_area face, traces.right_area face, traces.top_area face, traces.left_area face]
  unfold Integration.Polynomial.Rectangle.Boundary.Assembly.exteriorSides
    Riemann.Periods.BilinearGridBoundary.exteriorJoins
  have horizontal := FiniteSum.Fin.sumFin_congr (fun column : Fin (PieceIndices.columns (partitions.get position)) =>
    show
    Stokes.edgeArea (face.corners column.succ (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft
        (face.corners column.castSucc (Fin.last (PieceIndices.rows (partitions.get position)))).upperRight -
      Stokes.edgeArea (face.corners column.succ 0).lowerLeft (face.corners column.castSucc 0).lowerRight =
      Stokes.edgeArea (face.corners column.castSucc 0).lowerRight (face.corners column.succ 0).lowerLeft -
        Stokes.edgeArea (face.corners column.castSucc (Fin.last (PieceIndices.rows (partitions.get
          position)))).upperRight
          (face.corners column.succ (Fin.last (PieceIndices.rows (partitions.get position)))).upperLeft by
    simp only [Stokes.edgeArea]
    ring1)
  rw [horizontal]
  simp only [FiniteSum.Fin.sumFin_sub]
  ring1

end FacePerimeterTraces
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PerimeterTraces
