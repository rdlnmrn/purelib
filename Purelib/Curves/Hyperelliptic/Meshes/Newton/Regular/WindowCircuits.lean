module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Geometry.Grid.Walks

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.CellSeparation
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CellPolygon
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.Walks

open Purelib.Riemann.Meshes

open Purelib.Riemann.RootContinuation

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-! The fine-cell circuit compiler inside an original regular cell retains
no branch word. Its full polygon and connector areas remain in the formula. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces RegularFace BranchHole)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank (CircuitPartition)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalRegularFaces (OriginalRegularFaces)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

/-- A circuit partition containing no original branch-hole cell retains the empty branch walk. -/
private theorem kept_empty {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {branches : BranchIsolation.Data curve} {higher : 1 < curve.polynomial.natDegree}
    {bank : Branches.BranchCellBank curve branches higher} {faces : PuncturedGridFaces.PuncturedFaces bank}
    {start : Data.Gaussian.Basic.Canonical} {tree : RowCircuitOrder.CellCircuits bank.grid start}
    (partition : BranchCellBank.CircuitPartition faces tree)
    (absent : ∀ hole : PuncturedGridFaces.BranchHole bank, hole.cell ∉ tree.cells) :
    partition.kept.product = Walk.nil start := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | hole location =>
      exact (absent location.hole (location.cell_eq.symm ▸ List.mem_cons_self)).elim
  | append first last ihFirst ihLast =>
      change first.kept.product.append last.kept.product = _
      rw [ihFirst (fun hole member => absent hole (List.mem_append_left _ member)),
        ihLast (fun hole member => absent hole (List.mem_append_right _ member))]
      rfl

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational}
  {grid : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
    {face : Purelib.Riemann.Meshes.PuncturedGridFaces.RegularFace original}
  {current : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}

/-- A shrunken branch hole lies strictly inside its own original branch cell, so it cannot occur in the fine circuit of
an original regular cell. -/
theorem window_hole_absent (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face)
    (hole : PuncturedGridFaces.BranchHole grid.punctured.bank.toBranchCellBank) :
    hole.cell ∉ region.window.circuits.cells := by
  intro member
  have inside := (region.window.circuits_member.mp member).2
  have strict : hole.cell.box.StrictInterior (original.cell hole.index).box := by
    rw [hole.cell_eq]
    exact grid.shrunk.cell_strict hole.index
  have anchor := hole.cell.box.contains_anchor
  have originalInside : (original.cell hole.index).box.StrictContains hole.cell.box.anchor :=
    ⟨strict.left.trans_le anchor.1, anchor.2.1.trans_lt strict.right,
      strict.bottom.trans_le anchor.2.2.1, anchor.2.2.2.trans_lt strict.top⟩
  exact face.unassigned hole.index (CellSeparation.cells_eq_of_common_point original.grid
    (original.cell_mem hole.index) face.member originalInside (inside.contains anchor)).symm

/-- No branch circuit remains in the original regular-cell window. -/
theorem fine_kept_empty (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) {sheet : Fin 2}
    (prepared : Window.OrderedBranches grid.faces region.window current.edges current.vertices sheet) :
    prepared.partition.kept.product = Walk.nil face.cell.box.anchor := by
  apply Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.kept_empty
  intro hole member
  have same := prepared.ordered.tree_eq
  exact Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.window_hole_absent region hole (same ▸ member)

/-- This concerns the literal fine-window compiler on the retained lifted edge bank; it does not replace the ordered
global period programs. -/
theorem fine_compiled_word_empty (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) {sheet : Fin 2}
    (prepared : Window.OrderedBranches grid.faces region.window current.edges current.vertices sheet) :
    prepared.compiled.word = [] := by
  rw [prepared.compiled.word_eq, Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.fine_kept_empty region
    prepared]
  rfl

/-- Internal regular polygons are retained along with all connector terms. There is no hidden branch polygon in this
local comparison. -/
theorem resplit_window_area (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (sheet : Fin 2)
    (value : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    let prepared := Window.prepareBranches grid.faces region.window current.edges current.vertices sheet
    current.edges.chainArea current.vertices value
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet =
      AreaTerm.total value prepared.compiled.areaTerms := by
  intro prepared
  have area := prepared.areas value anti
  rw [Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.fine_compiled_word_empty region prepared] at area
  have boundary := grid.shrunk.included.cell_boundary_comparison face.cell face.member region.window
    current.edges current.vertices (fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank
      point member).toLoop)
  exact (boundary.areas value anti sheet).trans (area.trans (zero_add _))

/-- The same fine compiler also keeps exactly the regular boundary totals, which are the small factors in its connector
area terms. -/
theorem resplit_window_value (region : NewtonOriginalRegularFaces.OriginalRegularFaces grid face) (sheet : Fin 2)
    (value : Stokes.OrientedEdge current.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    let prepared := Window.prepareBranches grid.faces region.window current.edges current.vertices sheet
    current.edges.chainValue current.vertices value
      (grid.shrunk.included.resplit face.boundary (face.cell.anchor_mem face.member)) sheet =
      CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value occurrence.word)
        prepared.compiled.regulars := by
  intro prepared
  have values := prepared.values value anti
  rw [Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits.fine_compiled_word_empty region prepared] at values
  have boundary := grid.shrunk.included.cell_boundary_comparison face.cell face.member region.window
    current.edges current.vertices (fun point member => (BranchCellBank.referenceAt grid.punctured.bank.toBranchCellBank
      point member).toLoop)
  exact (boundary.values value anti sheet).trans (values.trans (zero_add _))

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Regular.WindowCircuits
