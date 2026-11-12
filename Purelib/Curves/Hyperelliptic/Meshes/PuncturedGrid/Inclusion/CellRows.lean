module

public import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.EdgeRows
public import Purelib.Polynomial.Geometry.Grid.FromPartition
public import Purelib.Polynomial.Geometry.Grid.Rectangle.Cuts
public import Purelib.Polynomial.Geometry.Grid.WindowBoundary
public import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Data.Vector.Dependent.Subtype
import Purelib.Riemann.Paths.ClearBoxPathWinding
public import Purelib.RootIsolation.SquareRoot.Grid.Inclusion.CellPolygon
public import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence

/-! # Original regular-face side rows on one genuinely local cut grid

The original ambient-indexed edge bank, cached cell restriction and actual
cut partition remain inputs. Only missing local grid frames, local edge
rows and their joined paths are newly prepared. The four actual old side
occurrences retain their orientation and use the original corner references.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Vector (DependentVector)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Rational (Box)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames RootEdgeBank)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} (old : RootEdgeBank frames) (face : RegularFace bank)
variable (coarse : frames.CellRestriction face.cell face.member) {points : List Canonical}
variable (cuts : CutPartition face.cell.box points)

/-- All four original oriented boundary endpoints belong to the actual retained fine cut grid. -/
theorem boundary_vertices {fine : ClearGrid curve.polynomial face.cell.box}
    (factory : fine = ClearGrid.ofPartition cuts face.clearance) :
    FromStates.ContainsPathVertices fine (CellBoundary.Cell.boundaryWalk face.cell face.member).path := by
  have bounds := ClearGrid.ofPartition_bounds_of_eq cuts face.clearance factory
  change (face.cell.box.xLower ∈ fine.vertical.map ClearGrid.VerticalLine.coordinate ∧
      face.cell.box.yLower ∈ fine.horizontal.map ClearGrid.HorizontalLine.coordinate) ∧
    (face.cell.box.xUpper ∈ fine.vertical.map ClearGrid.VerticalLine.coordinate ∧
      face.cell.box.yLower ∈ fine.horizontal.map ClearGrid.HorizontalLine.coordinate) ∧
    (face.cell.box.xUpper ∈ fine.vertical.map ClearGrid.VerticalLine.coordinate ∧
      face.cell.box.yUpper ∈ fine.horizontal.map ClearGrid.HorizontalLine.coordinate) ∧
    (face.cell.box.xLower ∈ fine.vertical.map ClearGrid.VerticalLine.coordinate ∧
      face.cell.box.yUpper ∈ fine.horizontal.map ClearGrid.HorizontalLine.coordinate) ∧
    (face.cell.box.xLower ∈ fine.vertical.map ClearGrid.VerticalLine.coordinate ∧
      face.cell.box.yLower ∈ fine.horizontal.map ClearGrid.HorizontalLine.coordinate)
  exact ⟨⟨bounds.1, bounds.2.2.1⟩, ⟨bounds.2.1, bounds.2.2.1⟩,
    ⟨bounds.2.1, bounds.2.2.2⟩, ⟨bounds.1, bounds.2.2.2⟩, ⟨bounds.1, bounds.2.2.1⟩⟩

/-- One materialized local fine bank retains the old inputs, every whole factory, window and four old side occurrences.

The original boundary walk is retained once. Each of its literal finite
positions stores one old connection, one actual local segment split and
two new signed joined paths; no function bank reexecutes those factories.
-/
abbrev CellRows :=
  {value : RootEdgeBank frames × frames.CellRestriction face.cell face.member × CutPartition face.cell.box points //
    value = (old, coarse, cuts)} ×
  (Σ fine : {value : ClearGrid curve.polynomial face.cell.box //
      value = ClearGrid.ofPartition cuts face.clearance},
  Σ fineFrames : {value : RootFrames fine.val // value = frames.extend fine.val},
  Σ edges : {value : RootEdgeBank fineFrames.val // value = RootEdgeBank.build fineFrames.val},
  Σ _window : {value : WindowBoundary.Window fine.val face.cell.box //
      value = WindowBoundary.Window.build fine.val face.cell.box
        (ClearGrid.ofPartition_bounds_of_eq cuts face.clearance fine.property).1
        (ClearGrid.ofPartition_bounds_of_eq cuts face.clearance fine.property).2.1
        (ClearGrid.ofPartition_bounds_of_eq cuts face.clearance fine.property).2.2.1
        (ClearGrid.ofPartition_bounds_of_eq cuts face.clearance fine.property).2.2.2},
  Σ boundary : {value : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor //
      value = CellBoundary.Cell.boundaryWalk face.cell face.member},
  DependentVector (fun index : Fin boundary.val.edgeCount =>
    let selected := boundary.val.edgeAt index
    let onFine := boundary.val.edgeAt_vertices fine.val
      (Eq.mpr (congrArg (fun value : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor =>
        FromStates.ContainsPathVertices fine.val value.path) boundary.property)
        (boundary_vertices face cuts fine.property)) index
    let reference := (LoopMonodromy.BranchCellBank.referenceAt bank selected.1 selected.2.2.vertices.1).toLoop
    {value : old.EdgeComparison selected.2.2 onFine.1 onFine.2 edges.val fineFrames.property reference //
      value = old.compareEdge selected.2.2 onFine.1 onFine.2 edges.val fineFrames.property reference}))

/-- Build the actual same-face local bank, window and all four retained old-side comparisons once.

New frame isolation is restricted to Cartesian vertices absent from the
whole old frame bank. The two directed rows of every new positive edge
are genuine new preparations. Each side/sheet path invokes the original
joined trace once; its newly created stationary joins still need their
own observation payments.
-/
def buildCellRows : CellRows old face coarse cuts :=
  let fine := ClearGrid.ofPartition cuts face.clearance
  let fineFrames := frames.extend fine
  let edges := RootEdgeBank.build fineFrames
  let bounds := ClearGrid.ofPartition_bounds cuts face.clearance
  let window := WindowBoundary.Window.build fine face.cell.box bounds.1 bounds.2.1 bounds.2.2.1 bounds.2.2.2
  let boundary := CellBoundary.Cell.boundaryWalk face.cell face.member
  have vertices := boundary_vertices face cuts (fine := fine) rfl
  let entries := Data.Vector.DependentVector.ofFnWithEq fun index : Fin boundary.edgeCount =>
    let selected := boundary.edgeAt index
    let onFine := boundary.edgeAt_vertices fine vertices index
    let reference := (LoopMonodromy.BranchCellBank.referenceAt bank selected.1 selected.2.2.vertices.1).toLoop
    old.compareEdge selected.2.2 onFine.1 onFine.2 edges rfl reference
  (⟨(old, coarse, cuts), rfl⟩,
    ⟨⟨fine, rfl⟩, ⟨fineFrames, rfl⟩, ⟨edges, rfl⟩, ⟨window, rfl⟩, ⟨boundary, rfl⟩, entries⟩)

namespace CellRows

variable {old face coarse cuts} (retained : CellRows old face coarse cuts)

/-- Read the original complete edge bank, same cached coarse restriction and same cut partition together. -/
def originals :
    RootEdgeBank frames × frames.CellRestriction face.cell face.member × CutPartition face.cell.box points :=
  retained.1.val

/-- Read the actual once-certified local coordinate grid. -/
def grid : ClearGrid curve.polynomial face.cell.box := retained.2.1.val

/-- Read the SAME original frame entries followed by the genuinely new local frames. -/
def localFrames : RootFrames retained.grid := retained.2.2.1.val

/-- Read both retained directed root-transport rows for every actual local positive edge. -/
def edges : RootEdgeBank retained.localFrames := retained.2.2.2.1.val

/-- Read the original same-grid window axes, line lookups and selected local cells. -/
def window : WindowBoundary.Window retained.grid face.cell.box := retained.2.2.2.2.1.val

/-- Read the literal original counterclockwise four-side walk, including its reversed top and left edges. -/
def boundary : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor := retained.2.2.2.2.2.1.val

/-- The whole original inputs remain cached unchanged. -/
theorem originals_eq : retained.originals = (old, coarse, cuts) := retained.1.property

/-- The retained local grid is the exact original cut-grid factory. -/
theorem grid_eq : retained.grid = ClearGrid.ofPartition cuts face.clearance := retained.2.1.property

/-- The actual local frame bank is the whole original missing-vertex extension. -/
theorem localFrames_eq : retained.localFrames = frames.extend retained.grid := retained.2.2.1.property

/-- The actual local edge bank is the whole original directed-row materializer. -/
theorem edges_eq : retained.edges = RootEdgeBank.build retained.localFrames := retained.2.2.2.1.property

/-- The retained old boundary is the whole original four-side factory. -/
theorem boundary_eq : retained.boundary = CellBoundary.Cell.boundaryWalk face.cell face.member :=
  retained.2.2.2.2.2.1.property

/-- The original four ordered boundary positions survive unchanged in this cache. -/
theorem boundary_count : retained.boundary.edgeCount = 4 :=
  (congrArg (fun value : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor => value.edgeCount)
    retained.boundary_eq).trans (CellBoundary.Cell.boundaryWalk_edgeCount face.cell face.member)

/-- Derive the local coarse-to-fine coordinate inclusion from the SAME cached restriction and partition. -/
theorem inclusion : Extension.CoordinateInclusion coarse.grid retained.grid :=
  Eq.mpr (congrArg (fun value : ClearGrid curve.polynomial face.cell.box =>
    Extension.CoordinateInclusion value retained.grid) coarse.grid_eq)
    (face.cell.grid_inclusion_of_eq cuts face.clearance retained.grid_eq)

/-- Every original retained side vertex occurs in the SAME local fine bank. -/
theorem boundary_onGrid : FromStates.ContainsPathVertices retained.grid retained.boundary.path :=
  Eq.mpr (congrArg (fun value : Walks.Walk bank.grid face.cell.box.anchor face.cell.box.anchor =>
    FromStates.ContainsPathVertices retained.grid value.path) retained.boundary_eq)
    (boundary_vertices face cuts retained.grid_eq)

/-- Read the exact cached comparison at one literal old oriented side occurrence.

The result retains the original full connection, actual local walk and both
materialized signed paths. Its source references are derived from the old
branch bank at those actual endpoints, not supplied as desired comparisons.
-/
def side (index : Fin retained.boundary.edgeCount) :
    let selected := retained.boundary.edgeAt index
    let onFine := retained.boundary.edgeAt_vertices retained.grid retained.boundary_onGrid index
    let reference := (LoopMonodromy.BranchCellBank.referenceAt bank selected.1 selected.2.2.vertices.1).toLoop
    old.EdgeComparison selected.2.2 onFine.1 onFine.2 retained.edges retained.localFrames_eq reference :=
  Data.Vector.DependentVector.getSubtypeValue retained.2.2.2.2.2.2 index

/-- An even loop reached by the SAME retained stem fixes both actual local-frame indices.

The reference is derived at the original old corner. Its stored ambient
is independent of the local bank ambient; no fine-vertex reference family
or extra root/query/Point preparation is supplied or constructed.
-/
theorem even_return {base : Canonical}
    (stem : Walks.Walk retained.grid face.cell.box.anchor base)
    (loop : Walks.Walk retained.grid base base) (turns : Int)
    (winding : Riemann.Paths.PreparedPathWinding.ClearPath.rawWinding loop.path = 8 * turns)
    (sheet : Fin 2) :
    RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target retained.edges loop sheet = sheet :=
  RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target_even_from_reference retained.edges
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop
    stem (FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid)
    loop turns winding sheet

/-- Every actual closed local walk fixes both frame sheets by the retained whole-face clearance.

The supplied stem is an actual grid walk from the original corner. Its
reverse gives the endpoint's literal grid incidence, including the empty
case. Closed winding is proved internally; no scalar winding or desired
signed-return certificate is supplied.
-/
theorem closed_return {base : Canonical}
    (stem : Walks.Walk retained.grid face.cell.box.anchor base)
    (loop : Walks.Walk retained.grid base base) (sheet : Fin 2) :
    RootIsolation.SquareRoot.Grid.EdgeBank.RootEdgeBank.target retained.edges loop sheet = sheet := by
  have anchor := FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid
  have onGrid := FromStates.ContainsPathVertices.start retained.grid stem.reverse.path (stem.reverse.vertices anchor)
  have inside := Polynomial.Geometry.ClearPath.InBox.ofWithin loop.path loop.withinAmbient onGrid.inside
  have zero := Riemann.Paths.ClearBoxPathWinding.ClearPath.rawWinding_zero_of_inBox face.clearance
    (Nat.lt_trans (by decide : 0 < 1) higher) loop.path inside
  exact retained.even_return stem loop 0 (zero.trans (by rfl)) sheet

/-- Reindex the SAME cached fine window to the retained coarse cell's whole box identity.

This operation changes no selected axis, line or cell. Its index equality
is the original cell-restriction readback, not equality inferred from points.
-/
def coarseWindow : WindowBoundary.Window retained.grid coarse.cell.val.box :=
  retained.window.castBox coarse.cell.property.2

/-- Derive the actual lifted boundary comparison from the original corner reference.

The original local coarse boundary is resplit in its retained order. Its
endpoints are transported by the cached cell's whole box identity, while
the target is exactly the already retained fine window boundary. No
fine-vertex winding-reference family or desired chain relation is supplied.
-/
theorem boundary_comparison (vertices : VertexBank retained.grid) :
    RootEdgeBank.ChainComparison retained.edges vertices
      ((retained.inclusion.resplit
        (CellBoundary.Cell.boundaryWalk coarse.cell.val coarse.cell.property.1)
        (ClearGrid.Cell.anchor_mem coarse.cell.val coarse.cell.property.1)).castEndpoints
          (congrArg Box.anchor coarse.cell.property.2)
          (congrArg Box.anchor coarse.cell.property.2))
      retained.window.boundary := by
  have anchor := FromStates.ContainsPathVertices.start retained.grid retained.boundary.path retained.boundary_onGrid
  have compared := retained.inclusion.cell_boundary_comparison_anchored
    coarse.cell.val coarse.cell.property.1 retained.coarseWindow retained.edges vertices
    (LoopMonodromy.BranchCellBank.referenceAt bank face.cell.box.anchor
      (face.cell.anchor_mem face.member)).toLoop anchor
  have transported := Polynomial.Geometry.Grid.AxisChainCoherence.RootEdgeBank.ChainComparison.castEndpoints
    compared (congrArg Box.anchor coarse.cell.property.2)
    (congrArg Box.anchor coarse.cell.property.2)
  have boundaryEq := WindowBoundary.Window.castBox_boundary coarse.cell.property.2 retained.window
  exact Eq.mp (congrArg (fun target => RootEdgeBank.ChainComparison
    retained.edges vertices
      ((retained.inclusion.resplit
        (CellBoundary.Cell.boundaryWalk coarse.cell.val coarse.cell.property.1)
        (ClearGrid.Cell.anchor_mem coarse.cell.val coarse.cell.property.1)).castEndpoints
          (congrArg Box.anchor coarse.cell.property.2)
          (congrArg Box.anchor coarse.cell.property.2)) target) boundaryEq) transported

/-- Materialize one coordinate-index bank and retain its derived actual boundary comparison.

The root frames, directed edge preparations, original side comparisons and
window are read from the existing retained product. Only the pure finite
vertex-index bank is newly built; no root/query/Point or path is rerun.
-/
def compareBoundary :
    {vertices : VertexBank retained.grid //
      vertices = VertexBank.build retained.grid ∧
      RootEdgeBank.ChainComparison retained.edges vertices
        ((retained.inclusion.resplit
          (CellBoundary.Cell.boundaryWalk coarse.cell.val coarse.cell.property.1)
          (ClearGrid.Cell.anchor_mem coarse.cell.val coarse.cell.property.1)).castEndpoints
            (congrArg Box.anchor coarse.cell.property.2)
            (congrArg Box.anchor coarse.cell.property.2))
        retained.window.boundary} :=
  let vertices := VertexBank.build retained.grid
  ⟨vertices, rfl, retained.boundary_comparison vertices⟩

end CellRows

/-- An actual retained support grid determines the once-built same-face cut partition and complete local side bank. -/
abbrev GridCellRows {supportAmbient : Geometry.Rational.Box}
    (support : ClearGrid curve.polynomial supportAmbient) :=
  Σ cuts : {value : Rectangle.Cuts.Partition support face.cell.box //
      value = Rectangle.Cuts.Partition.build support face.cell.box face.cell.box_proper},
  CellRows old face coarse cuts.val

/-- Construct the local partition directly from the SAME supplied support grid, then build the retained four-side bank.

Only this genuinely new partition and its local numerical/root geometry are
materialized. The source support grid, original side rows and every retained
query/Point/Entry remain independent existing inputs; no old cache is rerun.
-/
def buildGridCellRows {supportAmbient : Geometry.Rational.Box}
    (support : ClearGrid curve.polynomial supportAmbient) : GridCellRows old face coarse support :=
  let cuts := Rectangle.Cuts.Partition.build support face.cell.box face.cell.box_proper
  let compared := buildCellRows old face coarse cuts
  ⟨⟨cuts, rfl⟩, compared⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion
