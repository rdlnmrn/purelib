module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows.Entries
public import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Geometry.Rational.Box.Content
import Purelib.Integration.Energy.AffineTriangle
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootPathTransport

/-! # Positive signed cells in the SAME retained local bank

The four original side rows calculate the corner sheets. An actual
contained old-anchor stem and clear-face return close the lifted cell.
The original quadrilateral supplies its two positive triangles and literal
oriented source occurrences. These are local fine indices, not old-mesh
triangle indices or a deformation of the supplied physical path.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Components.Basic (point)
open Purelib.Geometry.Rectangle (CutPartition)
open Purelib.Geometry.Rectangle.Partition
open Purelib.Geometry.Rational.Box
open Purelib.Integration.Energy
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Polygon

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {old : RootEdgeBank frames} {face : RegularFace bank}
variable {coarse : frames.CellRestriction face.cell face.member} {points : List Canonical}
variable {cuts : CutPartition face.cell.box points} (retained : CellRows old face coarse cuts)
variable (vertices : VertexBank retained.grid) (cell : ClearGrid.Cell curve.polynomial face.cell.box)
variable (member : cell ∈ retained.grid.cells) (sheet : Fin 2)

/-- The exact local quadrilateral with three successive cached corner transports.

The original bottom, right and reversed top rows are read in order. No
frame, transport preparation, Point, query or join is acquired here.
-/
def quadrilateral : IndexedQuadrilateral vertices.count :=
  let lowerRight := (retained.edges.edge (cell.bottomSide member)).forward.target sheet
  let upperRight := (retained.edges.edge (cell.rightSide member)).forward.target lowerRight
  let upperLeft := (retained.edges.edge (cell.topSide member)).forward.target upperRight
  ⟨vertices.index cell.box.anchor (cell.anchor_mem member) sheet,
    vertices.index _ (cell.bottomSide member).vertices.2 lowerRight,
    vertices.index _ (cell.rightSide member).vertices.2 upperRight,
    vertices.index _ (cell.topSide member).vertices.2 upperLeft⟩

/-- One retained local quadrilateral together with its complete original factory identity. -/
abbrev LiftedCell :=
  {value : IndexedQuadrilateral vertices.count // value = retained.quadrilateral vertices cell member sheet}

/-- Materialize that pure local index quadrilateral once in the existing subtype container.

All root frames, directed rows and their selections are existing inputs.
The constructor retains the whole quadrilateral; later consumers use its
stored value, rather than executing an index-type factory to recover it.
-/
def liftCell : retained.LiftedCell vertices cell member sheet :=
  let quad := retained.quadrilateral vertices cell member sheet
  ⟨quad, rfl⟩

namespace LiftedCell

variable {retained vertices cell member sheet}
variable (lifted : retained.LiftedCell vertices cell member sheet)

/-- Read the actual retained quadrilateral with its four signed bounded indices. -/
def quad : IndexedQuadrilateral vertices.count := lifted.val

/-- The cached quadrilateral is the whole original pure corner-map factory result. -/
theorem quad_eq : lifted.quad = retained.quadrilateral vertices cell member sheet := lifted.property

/-- The first index is the original cell anchor on its supplied fine-frame sheet. -/
theorem first_eq : lifted.quad.first = vertices.index cell.box.anchor (cell.anchor_mem member) sheet :=
  congrArg IndexedQuadrilateral.first lifted.property

/-- The second index retains the original bottom row's actual target sheet. -/
theorem second_eq : lifted.quad.second = vertices.index _ (cell.bottomSide member).vertices.2
    ((retained.edges.edge (cell.bottomSide member)).forward.target sheet) :=
  congrArg IndexedQuadrilateral.second lifted.property

/-- The third index retains the original right row after that SAME bottom target. -/
theorem third_eq : lifted.quad.third = vertices.index _ (cell.rightSide member).vertices.2
    ((retained.edges.edge (cell.rightSide member)).forward.target
      ((retained.edges.edge (cell.bottomSide member)).forward.target sheet)) :=
  congrArg IndexedQuadrilateral.third lifted.property

/-- The fourth index retains the reversed top row after the SAME bottom and right targets. -/
theorem fourth_eq : lifted.quad.fourth = vertices.index _ (cell.topSide member).vertices.2
    ((retained.edges.edge (cell.topSide member)).forward.target
      ((retained.edges.edge (cell.rightSide member)).forward.target
        ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))) :=
  congrArg IndexedQuadrilateral.fourth lifted.property

/-- The four retained signed indices have the original cell's four exact coordinates. -/
theorem coordinates :
    vertices.coordinate lifted.quad.first = cell.box.anchor ∧
    vertices.coordinate lifted.quad.second = point cell.box.xUpper cell.box.yLower ∧
    vertices.coordinate lifted.quad.third = point cell.box.xUpper cell.box.yUpper ∧
    vertices.coordinate lifted.quad.fourth = point cell.box.xLower cell.box.yUpper := by
  rw [lifted.first_eq, lifted.second_eq, lifted.third_eq, lifted.fourth_eq]
  exact ⟨vertices.coordinate_index _ _ _, vertices.coordinate_index _ _ _,
    vertices.coordinate_index _ _ _, vertices.coordinate_index _ _ _⟩

/-- The first actual fine triangle has strictly positive oriented coordinate area. -/
theorem first_positive :
    0 < AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.second) (vertices.coordinate lifted.quad.third) := by
  rw [lifted.coordinates.1, lifted.coordinates.2.1, lifted.coordinates.2.2.1]
  change 0 < PreparedBoxTriangulation.coordinateArea (PreparedBoxTriangulation.lowerTriangle cell.box)
  rw [PreparedBoxTriangulation.lowerTriangle_area]
  exact Data.Rat.Fraction.Order.Field.div_pos_direct (Content.boxContent_pos_of_proper cell.box_proper) (by decide)

/-- The second actual fine triangle has strictly positive oriented coordinate area. -/
theorem second_positive :
    0 < AffineTriangle.coordinateTriangleArea (vertices.coordinate lifted.quad.first)
      (vertices.coordinate lifted.quad.third) (vertices.coordinate lifted.quad.fourth) := by
  rw [lifted.coordinates.1, lifted.coordinates.2.2.1, lifted.coordinates.2.2.2]
  change 0 < PreparedBoxTriangulation.coordinateArea (PreparedBoxTriangulation.upperTriangle cell.box)
  rw [PreparedBoxTriangulation.upperTriangle_area]
  exact Data.Rat.Fraction.Order.Field.div_pos_direct (Content.boxContent_pos_of_proper cell.box_proper) (by decide)

/-- The quad boundary is the SAME ordered bottom/right/top/left lifted bank walk.

The only reference stays at the old face anchor. Whole-face clearance
proves return internally along the actual supplied stem and fine boundary;
no per-fine-vertex reference or signed-return premise is supplied.
-/
theorem boundary_eq (stem : Walks.Walk retained.grid face.cell.box.anchor cell.box.anchor) :
    lifted.quad.boundary = retained.edges.indexedEdges vertices (CellBoundary.Cell.boundaryWalk cell member) sheet := by
  have closed := retained.closed_return stem (CellBoundary.Cell.boundaryWalk cell member) sheet
  rw [ClearGrid.Cell.boundaryWalk_sides] at closed
  change (retained.edges.edge (cell.leftSide member)).forward.target
    ((retained.edges.edge (cell.topSide member)).forward.target
      ((retained.edges.edge (cell.rightSide member)).forward.target
        ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))) = sheet at closed
  simp only [IndexedQuadrilateral.boundary, lifted.first_eq, lifted.second_eq,
    lifted.third_eq, lifted.fourth_eq, ClearGrid.Cell.boundaryWalk_sides,
    RootEdgeBank.indexedEdges, RootEdgeBank.indexedEdge]
  rw [closed]

/-- The SAME two triangles cancel exactly their diagonal, preserving all four ordered bank sides. -/
theorem incidence (stem : Walks.Walk retained.grid face.cell.box.anchor cell.box.anchor) :
    Stokes.EdgeReordering (lifted.quad.triangles.flatMap Stokes.OrientedTriangle.boundary)
      (retained.edges.indexedEdges vertices (CellBoundary.Cell.boundaryWalk cell member) sheet ++
        Stokes.pairedEdgeOccurrences [lifted.quad.diagonal]) :=
  Eq.mp (congrArg (fun boundary => Stokes.EdgeReordering
    (lifted.quad.triangles.flatMap Stokes.OrientedTriangle.boundary)
    (boundary ++ Stokes.pairedEdgeOccurrences [lifted.quad.diagonal])) (lifted.boundary_eq stem)) lifted.quad.incidence

/-- Every signed corner index follows its literal retained oriented boundary prefix. -/
theorem corner_index : ∀ corner,
    lifted.quad.corner corner = vertices.index (cell.cornerPrefix member corner).1
      (Eq.mpr (congrArg (FromStates.ContainsVertex retained.grid)
        (cell.cornerPrefix_point member corner)) (cell.corner_mem member corner))
      (EdgeBank.RootEdgeBank.target retained.edges (cell.cornerPrefix member corner).2 sheet) := by
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun index => Fin.elim0 index))))
  · rw [IndexedQuadrilateral.corner_zero]
    change lifted.quad.first = vertices.index cell.box.anchor (cell.anchor_mem member) sheet
    exact lifted.first_eq
  · change lifted.quad.corner (1 : Fin 4) = _
    rw [IndexedQuadrilateral.corner_one]
    change lifted.quad.second = vertices.index _ (cell.bottomSide member).vertices.2
      ((retained.edges.edge (cell.bottomSide member)).forward.target sheet)
    exact lifted.second_eq
  · change lifted.quad.corner (2 : Fin 4) = _
    rw [IndexedQuadrilateral.corner_two]
    change lifted.quad.third = vertices.index _ (cell.rightSide member).vertices.2
      ((retained.edges.edge (cell.rightSide member)).forward.target
        ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))
    exact lifted.third_eq
  · change lifted.quad.corner (3 : Fin 4) = _
    rw [IndexedQuadrilateral.corner_three]
    change lifted.quad.fourth = vertices.index _ (cell.topSide member).vertices.2
      ((retained.edges.edge (cell.topSide member)).forward.target
        ((retained.edges.edge (cell.rightSide member)).forward.target
          ((retained.edges.edge (cell.bottomSide member)).forward.target sheet)))
    exact lifted.fourth_eq

/-- Transport only the prefix endpoint and exact vertex lookup to the supplied geometric point.

The actual root sheet remains the target of that SAME ordered prefix.
This scalar index transport asserts no equality of independent Owners.
-/
theorem corner_index_at (corner : Fin 4) {point : Canonical}
    (same : (cell.cornerPrefix member corner).1 = point)
    (onGrid : FromStates.ContainsVertex retained.grid point) :
    lifted.quad.corner corner = vertices.index point onGrid
      (EdgeBank.RootEdgeBank.target retained.edges
        ((cell.cornerPrefix member corner).2.castEndpoints rfl same) sheet) := by
  cases same
  exact lifted.corner_index corner

/-- Every retained side source is a positive oriented occurrence of its actual fine triangle. -/
theorem sources_positive : ∀ source ∈ IndexedQuadrilateral.boundarySources,
    Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive source lifted.quad.faces :=
  lifted.quad.boundarySources_positive

/-- Those SAME source occurrences project to the exact signed bank-side sequence. -/
theorem sources_project (stem : Walks.Walk retained.grid face.cell.box.anchor cell.box.anchor) :
    IndexedQuadrilateral.boundarySources.map (fun source => source.project lifted.quad.faces) =
      retained.edges.indexedEdges vertices (CellBoundary.Cell.boundaryWalk cell member) sheet :=
  lifted.quad.boundarySources_project.trans (lifted.boundary_eq stem)

end LiftedCell

section Entries

variable (models : FaceModels frames face)

/-- Original face entries at the four actual corner-frame Owners in their signed side order. -/
abbrev CornerEntries :=
  Entry models cell.box.anchor
    ((retained.localFrames.frameAt cell.box.anchor (cell.anchor_mem member)).owners sheet) ×
  (Entry models (point cell.box.xUpper cell.box.yLower)
    ((retained.localFrames.frameAt _ (cell.bottomSide member).vertices.2).owners
      ((retained.edges.edge (cell.bottomSide member)).forward.target sheet)) ×
  (Entry models (point cell.box.xUpper cell.box.yUpper)
    ((retained.localFrames.frameAt _ (cell.rightSide member).vertices.2).owners
      ((retained.edges.edge (cell.rightSide member)).forward.target
        ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))) ×
  Entry models (point cell.box.xLower cell.box.yUpper)
    ((retained.localFrames.frameAt _ (cell.topSide member).vertices.2).owners
      ((retained.edges.edge (cell.topSide member)).forward.target
        ((retained.edges.edge (cell.rightSide member)).forward.target
          ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))))))

/-- Attach all four retained fine-corner Owners to the original old face through the SAME cached rows.

Only the supplied actual source Entry, three stored transport rows and
their retained selections are consumed. Entries carry reachability in Prop; no path is
extracted from that proof and no row, Point or stationary join is prepared.
-/
def cornerEntries
    (first : Entry models cell.box.anchor
      ((retained.localFrames.frameAt cell.box.anchor (cell.anchor_mem member)).owners sheet)) :
    retained.CornerEntries cell member sheet models :=
  let second := first.followRow
    (firstFrame := retained.localFrames.frameAt _ (cell.bottomSide member).vertices.1)
    (lastFrame := retained.localFrames.frameAt _ (cell.bottomSide member).vertices.2) (index := sheet)
    ((retained.edges.edge (cell.bottomSide member)).forward.row sheet)
    ⟨(cell.bottomSide member).vertices.1.inside, (cell.bottomSide member).vertices.2.inside⟩
  let third := second.followRow
    (firstFrame := retained.localFrames.frameAt _ (cell.rightSide member).vertices.1)
    (lastFrame := retained.localFrames.frameAt _ (cell.rightSide member).vertices.2)
    (index := (retained.edges.edge (cell.bottomSide member)).forward.target sheet)
    ((retained.edges.edge (cell.rightSide member)).forward.row
      ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))
    ⟨(cell.rightSide member).vertices.1.inside, (cell.rightSide member).vertices.2.inside⟩
  let fourth := third.followRow
    (firstFrame := retained.localFrames.frameAt _ (cell.topSide member).vertices.1)
    (lastFrame := retained.localFrames.frameAt _ (cell.topSide member).vertices.2)
    (index := (retained.edges.edge (cell.rightSide member)).forward.target
      ((retained.edges.edge (cell.bottomSide member)).forward.target sheet))
    ((retained.edges.edge (cell.topSide member)).forward.row
      ((retained.edges.edge (cell.rightSide member)).forward.target
        ((retained.edges.edge (cell.bottomSide member)).forward.target sheet)))
    ⟨(cell.topSide member).vertices.1.inside, (cell.topSide member).vertices.2.inside⟩
  (first, second, third, fourth)

/-- The complete supplied first Entry is retained unchanged in the corner product. -/
theorem cornerEntries_first
    (first : Entry models cell.box.anchor
      ((retained.localFrames.frameAt cell.box.anchor (cell.anchor_mem member)).owners sheet)) :
    (retained.cornerEntries cell member sheet models first).1 = first := by rfl

/-- The actual signed fine corners all retain the SAME old face-sheet index.

The old index is read from the actual supplied Entry, not copied from a
new frame label. Each original forward row preserves that old Entry sheet.
-/
theorem corner_sheets
    (first : Entry models cell.box.anchor
      ((retained.localFrames.frameAt cell.box.anchor (cell.anchor_mem member)).owners sheet)) :
    let entries := retained.cornerEntries cell member sheet models first
    entries.1.sheet = entries.2.1.sheet ∧ entries.1.sheet = entries.2.2.1.sheet ∧
      entries.1.sheet = entries.2.2.2.sheet := by
  dsimp only [cornerEntries]
  simp only [Entry.followRow_sheet, -eq_self, -iff_self]
  exact ⟨rfl, rfl, rfl⟩

end Entries

section Point

variable {retained vertices cell member}
variable {models : FaceModels frames face}
variable {stem : Walks.Walk retained.grid face.cell.box.anchor cell.box.anchor}
variable {count : Nat} {neighborhood : ContinuedNeighborhood curve.polynomial count}
variable {sample : ContinuedNeighborhood.Point neighborhood cell.box.anchor}
variable (classified : retained.PointEntry models stem (cell.anchor_mem member) sample)
variable (lifted : retained.LiftedCell vertices cell member classified.selected.index)

/-- The SAME supplied Point Owner attaches to the actual first signed fine-triangle index.

Only the already retained fine-frame selection and whole Owner/index
readback are composed. This does not create an observed OwnerJoin or
identify the Point Owner with a frame Owner by common coordinates.
-/
def PointEntry.cellSourceEquivalent : Approximation.Gaussian.Equivalence.NamedEquivalent
    (ownerName sample.owner) (ownerName (vertices.owner retained.localFrames lifted.quad.first)) :=
  Approximation.Gaussian.Equivalence.NamedEquivalent.transport rfl
    (congrArg (fun index => ownerName (vertices.owner retained.localFrames index)) lifted.first_eq).symm
    (classified.selected_equivalent vertices)

/-- The actual fine-corner attachment agrees with the retained Point's original old-face sheet.

The Point-to-frame selection is the original cached operational witness.
The three further corners retain this index by the same ordered row
propagation; primitive anchors and offsets are not identified by this law.
-/
theorem PointEntry.cell_corner_sheets :
    let entries := retained.cornerEntries cell member classified.selected.index models classified.frameEntry
    entries.1.sheet = classified.entry.sheet ∧ entries.2.1.sheet = classified.entry.sheet ∧
      entries.2.2.1.sheet = classified.entry.sheet ∧ entries.2.2.2.sheet = classified.entry.sheet := by
  rw [← classified.frameEntry_sheet]
  dsimp only [cornerEntries]
  simp only [Entry.followRow_sheet, -eq_self, -iff_self]
  exact ⟨rfl, rfl, rfl, rfl⟩

end Point

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.CellRows

end
