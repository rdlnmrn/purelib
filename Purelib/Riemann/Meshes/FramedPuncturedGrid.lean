module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
public import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
public import Purelib.Riemann.Meshes.PuncturedGridMesh
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Geometry.Rational.Box.Separation
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Data.Gaussian.Field

public section

/-!
# A retained punctured grid with genuine interior branch holes

The frame, branch rows and classified faces are cached together.  Existing
mesh refinements consume those faces without repeating branch isolation or
clearance construction.  Their exterior-minus-holes identity now uses the
actual subdivided outer walk, and every hole is strictly interior to it.
Two-sheet gluing and the global cut-surface primitives remain separate.
-/

namespace Purelib.Riemann.Meshes

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank FramedBranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces BranchHole)
open Purelib.Riemann.Meshes.PuncturedGridMesh (PuncturedMesh)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

set_option genInjectivity false in
/-- A retained framed branch-cell bank together with its exact punctured-face partition.

The original curve, branch-isolation data and degree bound remain indices of the bank and every stored regular face and
hole. -/
structure FramedPuncturedGrid (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) where
  /-- The original framed branch-cell bank with its exact curve and branch data. -/ bank :
    Curves.Hyperelliptic.Branches.FramedBranchCellBank curve branches higher
  /-- The retained punctured-face partition of the exact stored bank. -/ faces : PuncturedFaces bank.toBranchCellBank

constructive_injectivity FramedPuncturedGrid

namespace FramedPuncturedGrid

open Purelib.Data.Gaussian
open Purelib.Polynomial
open Purelib.Topology.Polygon

/-- Construct the exact punctured-face partition of the retained original framed bank. -/
@[expose] def ofBank (bank : Curves.Hyperelliptic.Branches.FramedBranchCellBank curve branches higher) :
  FramedPuncturedGrid curve branches higher :=
  ⟨bank, PuncturedFaces.build bank.toBranchCellBank⟩

/-- Build the original framed branch-cell bank and retain its exact punctured-face partition. -/
@[expose] def ofData (curve : Basic.HyperellipticCurve genus) (branches : BranchIsolation.Data curve)
    (higher : 1 < curve.polynomial.natDegree) : FramedPuncturedGrid curve branches higher :=
  ofBank (FramedBranchCellBank.ofData curve branches higher)

/-- Every original retained hole lies strictly inside the curve's ambient box. -/
theorem hole_interior (grid : FramedPuncturedGrid curve branches higher) (hole : BranchHole grid.bank.toBranchCellBank)
  :
    hole.cell.box.StrictInterior (Cuts.Ambient curve) := by
  rw [hole.cell_eq]
  exact grid.bank.holesInterior hole.index

/-- Original retained holes with distinct branch indices have separated boxes. -/
theorem holes_separated (grid : FramedPuncturedGrid curve branches higher)
    (first second : BranchHole grid.bank.toBranchCellBank) (different : first.index ≠ second.index) :
    first.cell.box.Separated second.cell.box := by
  rw [first.cell_eq, second.cell_eq]
  exact grid.bank.toBranchCellBank.cells_separated first.index second.index different

/-- Refine the original framed grid's retained regular faces into a coordinate mesh at the requested depth. -/
@[expose] def mesh (grid : FramedPuncturedGrid curve branches higher) (depth : Nat) : PuncturedMesh grid.faces depth :=
  PuncturedMesh.build grid.faces depth

/-- The retained coordinate mesh boundary equals the framed original exterior and inward hole boundaries.

The ambient-frame equation identifies the original grid perimeter while preserving the separate ordered hole
contributions. -/
theorem boundary_eq_exterior_and_holes (grid : FramedPuncturedGrid curve branches higher) {depth : Nat}
    (surface : PuncturedMesh grid.faces depth) (primitive : Basic.Canonical → Stokes.PrimitivePoint) :
    Stokes.edgeListArea (fun vertex => primitive (surface.mesh.coordinate vertex)) surface.mesh.triangulation.boundary =
      (PuncturedMesh.primitiveEdges primitive depth).walk grid.bank.exterior +
        Geometry.Grid.CellBoundary.sumValues (fun hole => (PuncturedMesh.primitiveEdges primitive depth).walk
          hole.inwardBoundary) grid.faces.holes := by
  rw [surface.boundary_eq_exterior_sub_holes]
  exact congrArg (fun exterior => exterior + _)
    (Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame.boundary_value grid.bank.frame _).symm

end FramedPuncturedGrid

end Purelib.Riemann.Meshes
