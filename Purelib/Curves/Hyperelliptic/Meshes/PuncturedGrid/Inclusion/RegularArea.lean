module
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.Reverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)

open Purelib.Topology.Mesh

@[expose] public section

/-! Original regular-cell excursions after subdivision. The original
ordered exterior decomposition retains these cells as area corrections;
their full subdivided boundaries and connector cross terms must survive. -/

namespace Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  (face : RegularFace bank) {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial
    (Ambient curve)}
  (included : Purelib.Polynomial.Geometry.Grid.Extension.CoordinateInclusion bank.grid grid)
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} (edges :
    RootEdgeBank frames) (vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank grid)
  (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
    Purelib.Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)

/-- Subdivision preserves this original regular cell's zero winding and actual sheet return, without identifying
independently chosen root frames. -/
theorem resplit_target (sheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet = sheet :=
  RootEdgeBank.target_even edges (BranchCellBank.referenceAt bank _ (face.cell.anchor_mem face.member)).toLoop _
    (included.vertex (face.cell.anchor_mem face.member)) 0
    ((included.resplit_winding _ (face.cell.anchor_mem face.member)).trans face.boundary_winding) sheet

variable {start : Purelib.Data.Gaussian.Basic.Canonical} (stem : Purelib.Polynomial.Geometry.Grid.Walks.Walk bank.grid
  start face.cell.box.anchor)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start)

include vertices reference

/-- The actual subdivided regular-cell excursion returns to its starting sheet, including its original connector. -/
theorem resplit_based_target (sheet : Fin 2) :
    RootEdgeBank.target edges (included.resplit (stem.based face.boundary) member) sheet = sheet := by
  have comparison := included.resplit_based edges vertices reference stem face.boundary member (face.cell.anchor_mem
    face.member)
  rw [comparison.targets sheet, Walk.based, RootEdgeBank.target_append edges, RootEdgeBank.target_append edges,
    face.resplit_target included edges, edges.target_reverse reference]

/-- Only the retraced connector's integral cancels. The retained boundary is the whole original cell, not one newly
selected regular face. -/
theorem resplit_based_value (value : OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) (sheet : Fin 2) :
    edges.chainValue vertices value (included.resplit (stem.based face.boundary) member) sheet =
      edges.chainValue vertices value (included.resplit face.boundary (face.cell.anchor_mem face.member))
        (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet) := by
  rw [(included.resplit_based edges vertices reference stem face.boundary member
    (face.cell.anchor_mem face.member)).values value anti sheet,
    Walk.based, RootEdgeBank.chainValue_append, RootEdgeBank.chainValue_append,
    face.resplit_target included edges]
  have cancelled := (ChainComparison.retrace (edges := edges) (vertices := vertices) reference
    (included.resplit stem (face.cell.anchor_mem face.member))).values value anti sheet
  rw [RootEdgeBank.chainValue_append] at cancelled
  change _ + _ = 0 at cancelled
  calc
    _ = edges.chainValue vertices value (included.resplit face.boundary (face.cell.anchor_mem face.member))
        (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet) +
        (edges.chainValue vertices value (included.resplit stem (face.cell.anchor_mem face.member)) sheet +
          edges.chainValue vertices value (included.resplit stem (face.cell.anchor_mem face.member)).reverse
            (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet)) := by ring1
    _ = _ := by rw [cancelled, add_zero]

/-- The ordered exterior reduction must pay this connector cross term even though the regular circuit returns to its
actual starting sheet. -/
theorem resplit_based_area (value : OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) (sheet : Fin 2) :
    edges.chainArea vertices value (included.resplit (stem.based face.boundary) member) sheet =
      edges.chainArea vertices value (included.resplit face.boundary (face.cell.anchor_mem face.member))
        (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet) +
      2 * BoundaryRibbon.area
        (edges.chainValue vertices value (included.resplit stem (face.cell.anchor_mem face.member)) sheet)
        (edges.chainValue vertices value (included.resplit face.boundary (face.cell.anchor_mem face.member))
          (RootEdgeBank.target edges (included.resplit stem (face.cell.anchor_mem face.member)) sheet)) := by
  rw [(included.resplit_based edges vertices reference stem face.boundary member
    (face.cell.anchor_mem face.member)).areas value anti sheet,
    Walk.based, RootEdgeBank.chainArea, edges.indexedEdges_append, edges.indexedEdges_append,
    face.resplit_target included edges, edges.indexedEdges_reverse vertices reference]
  exact RetracingWords.wordArea_conjugate value anti _ _

end Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace
