module
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Polynomial.Geometry.Grid.AxisWalks
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.FramedClearGrid
import Purelib.Polynomial.Geometry.Grid.RowCircuitOrder
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.CircuitStemGeometry

open Purelib.Polynomial.Geometry.Grid.FramedClearGrid

open Purelib.Polynomial.Geometry.Grid.RowCircuitOrder

open Purelib.Polynomial.Geometry.Grid.WindowBoundary

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)

open Purelib.Polynomial.Geometry.Grid.Walks (Walk)

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.RetracingWords

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

/-!
# The exterior as an ordered product of the actual common-root branch tours

The window expression first retains its original branch labels and regular
face occurrences. Its certified ascending stems then identify the remaining
circuits with the already prepared common-root branch loops. The exterior
comparison includes the actual mesh correction and the arriving sheet.
-/

namespace Purelib

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Pair)
open Purelib.Topology.Mesh.RetracingWords (wordArea AreaTerm)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Sewing.SewingRetraction
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open _root_.Purelib.Polynomial.Geometry.Grid.FramedClearGrid (AmbientFrame)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)

namespace Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

variable {polynomial : Purelib.Polynomial.Geometry.ClearPath.GaussianPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {grid : ClearGrid polynomial
  ambient}

/-- The retained full ambient grid window. -/
@[expose] def window (frame :
  AmbientFrame grid) : WindowBoundary.Window grid ambient :=
  let axes := frame.axes
  ⟨axes.x, axes.y, AxisWalks.lookup _ grid.vertical frame.xLower,
    AxisWalks.lookup _ grid.vertical frame.xUpper, AxisWalks.lookup _ grid.horizontal frame.yLower,
    AxisWalks.lookup _ grid.horizontal frame.yUpper,
    grid.cells.filter (fun cell => decide (cell.box.Refines ambient)), rfl⟩

/-- The window built from the retained ambient frame has exactly the original exterior boundary walk. -/
theorem window_boundary (frame :
  AmbientFrame grid) : frame.window.boundary = frame.boundary := rfl

end Polynomial.Geometry.Grid.FramedClearGrid.AmbientFrame

namespace Curves.Hyperelliptic.Meshes.PuncturedGrid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base}

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Each loop continues on the actual sheet left by its predecessor. -/
@[expose] def
  loopProduct
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) : List (BranchIsolation.Data.Index branches) →
    Walks.Walk base.bank.grid (Cuts.Ambient curve).anchor (Cuts.Ambient curve).anchor
  | [] => .nil _
  | index :: labels => (bank.rows.get index).reference.walk.append (bank.loopProduct labels)

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Concatenating retained branch labels concatenates their original based-loop products. -/
theorem
  loopProduct_append
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (first last : List (BranchIsolation.Data.Index branches)) :
    bank.loopProduct (first ++ last) = (bank.loopProduct first).append (bank.loopProduct last) := by
  induction first with
  | nil => rfl
  | cons index rest ih =>
      change (bank.rows.get index).reference.walk.append (bank.loopProduct (rest ++ last)) = _
      rw [ih]
      exact (Walk.append_assoc _ _ _).symm

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- One retained branch loop exchanges the actual arriving root sheet. -/
private theorem branch_target (bank :
  LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index
  branches) (sheet : Fin 2) :
    RootEdgeBank.target lifted.edges (bank.rows.get index).reference.walk sheet = BranchCutLifts.otherSheet sheet :=
  RootEdgeBank.target_odd lifted.edges (bank.rows.get index).reference.walk (FramedBranchCellBank.baseMember base.bank)
    0
    ((bank.rows.get index).reference.winding.trans (by decide)) sheet

end OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Consecutive labels are the actual root-closed pair program. Its second loop starts on the exchanged sheet and the
remaining product resumes on the original sheet, with equality of the complete indexed edge lists. -/
theorem
  loopProduct_pair_indexed
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    (first last : BranchIsolation.Data.Index branches) (labels : List (BranchIsolation.Data.Index branches)) (sheet :
      Fin 2)
    (pair : BasedBranchBank.Pair bank first last sheet) :
    lifted.edges.indexedEdges lifted.vertices (bank.loopProduct (first :: last :: labels)) sheet =
      pair.closed.indexed ++ lifted.edges.indexedEdges lifted.vertices (bank.loopProduct labels) sheet := by
  rw [pair.indexed, Purelib.Data.List.Append.append_assoc]
  simp only [loopProduct,
    RootEdgeBank.indexedEdges_append,
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.branch_target
    bank, BranchCutLifts.otherSheet_other, -eq_self, -iff_self]
  rfl

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Canonicalizing the actual located branch cell yields its original retained labelled loop. -/
private theorem canonical_loop (bank :
  LiftedPuncturedGrid.BasedBranchBank lifted) (index : BranchIsolation.Data.Index
  branches)
    (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (member : cell ∈ base.bank.grid.cells)
    (equal : cell = base.bank.cell index) :
    ((Grid.connect base.bank.grid cell.box.anchor (Cuts.Ambient curve).anchor (cell.anchor_mem member)
      (FramedBranchCellBank.baseMember base.bank)).reverse.based
      (CellBoundary.Cell.boundaryWalk cell member)) = (bank.rows.get index).reference.walk := by
  cases equal
  rw [(bank.rows.get index).reference_eq, (bank.rows.get index).stem_eq, (bank.rows.get index).boundary_eq]
  rfl

end OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Canonicalizing a retained branch leaf produces its original labelled bank entry, not an independently prepared or
relabelled branch circuit. -/
theorem
  canonicalized_product
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    {tree : RowCircuitOrder.CellCircuits base.bank.grid (Cuts.Ambient curve).anchor}
    (partition : BranchCellBank.CircuitPartition base.faces tree) :
    (partition.kept.canonicalize (FramedBranchCellBank.baseMember base.bank)).product = bank.loopProduct
      partition.labels := by
  induction partition with
  | nil => rfl
  | regular => rfl
  | @hole cell member stem location =>
      change _ = (bank.rows.get location.hole.index).reference.walk.append (.nil _)
      rw [Walk.append_nil]
      exact
        OrderedBasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.canonical_loop
        bank location.hole.index cell member (location.cell_eq.symm.trans location.hole.cell_eq)
  | append first last ihFirst ihLast =>
      change (first.kept.canonicalize _).product.append (last.kept.canonicalize _).product = _
      rw [ihFirst, ihLast, ← bank.loopProduct_append]
      rfl

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- The retained ascending-stem certificates compare the actual kept circuit product with the original branch-bank loop
product. -/
theorem
  ordered_comparison
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted)
    {window : Polynomial.Geometry.Grid.WindowBoundary.Window base.bank.grid (Cuts.Ambient curve)} {sheet : Fin 2}
    (prepared : Window.OrderedBranches base.faces window lifted.edges lifted.vertices sheet) :
    RootEdgeBank.ChainComparison lifted.edges lifted.vertices prepared.partition.kept.product
      (bank.loopProduct prepared.labels) := by
  have stems : CellCircuits.AscendingStems lifted.edges lifted.vertices prepared.ordered.tree := by
    rw [prepared.ordered.tree_eq]
    exact window.ascending_stems
  have same := (CircuitPartition.kept_stems prepared.partition stems).canonicalize_comparison
    (fun point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop)
      (FramedBranchCellBank.baseMember base.bank)
  exact same.trans (ChainComparison.of_eq
    ((bank.canonicalized_product prepared.partition).trans (congrArg bank.loopProduct prepared.labels_eq.symm)))

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

set_option genInjectivity false in
/-- This cache joins the existing exterior, original branch bank and shared mesh. Every label occurs exactly once, in
the proved geometric order. -/
structure
  Ordered
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin 2) where
  /-- The retained full ambient grid window. -/ window : Polynomial.Geometry.Grid.WindowBoundary.Window base.bank.grid
    (Cuts.Ambient curve)
  /-- The window boundary is exactly the original physical exterior walk. -/ exterior_eq : window.boundary =
    base.bank.exterior
  /-- The cached ordered branch partition on this exact window and starting sheet. -/ prepared : Window.OrderedBranches
    base.faces window lifted.edges lifted.vertices sheet
  /-- Every original retained branch label occurs in the cached ordered selection. -/ complete : ∀ index, index ∈
    prepared.labels
  /-- The cached ordered product of actual original branch loops. -/ walk : Walks.Walk base.bank.grid (Cuts.Ambient
    curve).anchor (Cuts.Ambient curve).anchor
  /-- The walk is exactly the original bank's loop product in retained label order. -/ walk_eq : walk = bank.loopProduct
    prepared.labels
  /-- The cached actual lifted indexed edge word. -/ word : List (Stokes.OrientedEdge lifted.vertices.count)
  /-- The indexed word is exactly the lift of the retained walk on the supplied arriving sheet. -/ word_eq : word =
    lifted.edges.indexedEdges lifted.vertices walk sheet
  /-- The retained chain comparison between the actual kept circuit product and cached branch walk. -/ comparison :
    RootEdgeBank.ChainComparison lifted.edges lifted.vertices prepared.partition.kept.product walk
  /-- The signed original mesh-face corrections for every retained regular circuit occurrence. -/ corrections :
    CircuitPartition.FaceCorrections lifted.mesh prepared.compiled.regulars

constructive_injectivity Ordered

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank (Ordered)

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

/-- Cache the full ambient branch order, actual indexed loop product and original signed face corrections. -/
@[expose] def
  ordered
  (bank : LiftedPuncturedGrid.BasedBranchBank lifted) (sheet : Fin 2) :
  Ordered bank sheet :=
  by
  let window := base.bank.frame.window
  let prepared := Window.prepareBranches base.faces window lifted.edges lifted.vertices sheet
  let walk := bank.loopProduct prepared.labels
  refine ⟨window, rfl, prepared, ?_, walk, rfl, lifted.edges.indexedEdges lifted.vertices walk sheet,
    rfl, bank.ordered_comparison prepared, OrderedBranches.corrections prepared lifted.mesh⟩
  intro index
  exact (prepared.selected index).mpr (base.bank.cell index).box_refines

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

namespace BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered

variable {bank : BasedBranchBank
  lifted} {sheet : Fin 2} (ordered :
  Ordered bank
  sheet)

/-- The cached ordered branch walk and original exterior have the same actual final root sheet. -/
theorem
  target
  : RootEdgeBank.target lifted.edges ordered.walk sheet = RootEdgeBank.target lifted.edges base.bank.exterior sheet :=
  by
  rw [← ordered.exterior_eq]
  exact (ordered.comparison.targets sheet).symm.trans
    (ordered.prepared.compiled.kept_target_eq.trans ordered.prepared.target.symm)

/-- The actual kept word and cached ordered branch word have equal sums for every antisymmetric edge valuation. -/
theorem
  word_values
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    SewingRetraction.wordValue value ordered.prepared.compiled.word = SewingRetraction.wordValue value ordered.word :=
      by
  rw [ordered.prepared.compiled.word_eq, ordered.word_eq]
  exact ordered.comparison.values value anti sheet

/-- The actual kept word and cached ordered branch word have equal cumulative areas for every antisymmetric edge
valuation. -/
theorem
  word_areas
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    RetracingWords.wordArea value ordered.prepared.compiled.word = RetracingWords.wordArea value ordered.word := by
  rw [ordered.prepared.compiled.word_eq, ordered.word_eq]
  exact ordered.comparison.areas value anti sheet

/-- The physical exterior area equals the cached branch-word area plus all retained ordered area correction terms. -/
theorem
  exterior_areas
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    lifted.edges.chainArea lifted.vertices value base.bank.exterior sheet = RetracingWords.wordArea value ordered.word +
      AreaTerm.total value ordered.prepared.compiled.areaTerms := by
  rw [← ordered.exterior_eq]
  exact (ordered.prepared.areas value anti).trans
    (congrArg (fun branchArea => branchArea + AreaTerm.total value ordered.prepared.compiled.areaTerms)
      (ordered.word_areas value anti))

/-- The physical exterior remains explicit. The correction uses the same located triangles as the owner-aware local
primitive comparisons. -/
theorem
  exterior_values
  (value : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    lifted.edges.chainValue lifted.vertices value base.bank.exterior sheet = SewingRetraction.wordValue value
      ordered.word +
      SewingRetraction.faceValue lifted.mesh.triangulation.faces value ordered.corrections.terms := by
  rw [← ordered.exterior_eq]
  exact (OrderedBranches.face_values ordered.prepared ordered.corrections value anti).trans
    (congrArg (fun branchValue => branchValue + SewingRetraction.faceValue lifted.mesh.triangulation.faces value
      ordered.corrections.terms)
      (ordered.word_values value anti))

end BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank.Ordered
end Curves.Hyperelliptic.Meshes.PuncturedGrid
end Purelib

end
